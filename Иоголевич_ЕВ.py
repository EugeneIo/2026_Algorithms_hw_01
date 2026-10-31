import sys
import signal
import heapq
from collections import deque

stop = False


def on_sigterm(signum, frame):
    global stop
    stop = True


def main():
    signal.signal(signal.SIGTERM, on_sigterm)

    inp = sys.stdin.buffer
    first = inp.readline()
    if not first:
        return

    parts = first.split()
    if len(parts) < 2:
        return

    n = int(parts[0])
    m = int(parts[1])

    orig_out = [[] for _ in range(n + 1)]
    orig_in_deg = [0] * (n + 1)

    out_dyn = [set() for _ in range(n + 1)]
    in_dyn = [set() for _ in range(n + 1)]

    for i in range(1, n + 1):
        line = inp.readline()
        if not line:
            vals = []
        else:
            parts = line.split()
            if parts:
                vals = list(map(int, parts))
            else:
                vals = []

        orig_out[i] = vals
        out_dyn[i] = set(vals)

        for v in vals:
            in_dyn[v].add(i)
            orig_in_deg[v] += 1

    state = [0] * (n + 1)
    processed = 0
    have_valid_answer = False

    queue = deque()
    in_queue = [False] * (n + 1)

    heap = []
    heap_ready = False

    indeg_arr = [0] * (n + 1)

    def add_queue(v):
        if state[v] == 0 and not in_queue[v]:
            queue.append(v)
            in_queue[v] = True

    def udali(v, mark):
        nonlocal processed

        if state[v] != 0:
            return

        state[v] = mark
        processed += 1

        for to in out_dyn[v]:
            if state[to] == 0:
                if v in in_dyn[to]:
                    in_dyn[to].remove(v)
                    if len(in_dyn[to]) < 2:
                        add_queue(to)

        for fr in in_dyn[v]:
            if state[fr] == 0:
                if v in out_dyn[fr]:
                    out_dyn[fr].remove(v)
                    if len(out_dyn[fr]) < 2:
                        add_queue(fr)

        out_dyn[v].clear()
        in_dyn[v].clear()

    def ves(v):
        iz = len(in_dyn[v])
        oz = len(out_dyn[v])
        s = iz + oz
        if s == 0:
            return 0.0
        return (iz * oz) / s

    def push_heap(v):
        if state[v] == 0 and heap_ready:
            heapq.heappush(heap, (-ves(v), v))

    def rebuild_heap():
        heap.clear()
        for v in range(1, n + 1):
            if state[v] == 0:
                heap.append((-ves(v), v))
        heapq.heapify(heap)

    def extract_heap():
        while not stop:
            if not heap:
                rebuild_heap()
                if not heap:
                    return None

            neg_w, v = heapq.heappop(heap)

            if state[v] != 0:
                continue

            actual_w = ves(v)

            if neg_w != -actual_w:
                heapq.heappush(heap, (-actual_w, v))
                continue

            return actual_w, v

        return None

    def shimaem(v):
        if state[v] != 0:
            return

        din = len(in_dyn[v])
        dout = len(out_dyn[v])

        if din == 0 or dout == 0:
            udali(v, -1)
            return

        if din == 1:
            j = next(iter(in_dyn[v]))

            if state[j] != 0:
                in_dyn[v].discard(j)
                add_queue(v)
                return

            if j in out_dyn[v]:
                udali(j, 1)
                return

            for i in list(out_dyn[v]):
                if stop:
                    return

                if state[i] != 0:
                    continue

                if i == j:
                    udali(j, 1)
                    return

                if i not in out_dyn[j]:
                    out_dyn[j].add(i)
                    in_dyn[i].add(j)

                    if heap_ready:
                        push_heap(j)
                        push_heap(i)

            out_dyn[j].discard(v)
            in_dyn[v].discard(j)

            if len(out_dyn[j]) < 2:
                add_queue(j)

            if heap_ready:
                push_heap(j)

            udali(v, -1)
            return

        if dout == 1:
            j = next(iter(out_dyn[v]))

            if state[j] != 0:
                out_dyn[v].discard(j)
                add_queue(v)
                return

            if j in in_dyn[v]:
                udali(j, 1)
                return

            for i in list(in_dyn[v]):
                if stop:
                    return

                if state[i] != 0:
                    continue

                if i == j:
                    udali(j, 1)
                    return

                if i not in in_dyn[j]:
                    in_dyn[j].add(i)
                    out_dyn[i].add(j)

                    if heap_ready:
                        push_heap(i)
                        push_heap(j)

            out_dyn[v].discard(j)
            in_dyn[j].discard(v)

            if len(in_dyn[j]) < 2:
                add_queue(j)

            if heap_ready:
                push_heap(j)

            udali(v, -1)
            return

    def shimaem_graf():
        while queue and not stop:
            v = queue.popleft()
            in_queue[v] = False
            shimaem(v)

    def proverka(force=False):
        if not force and stop:
            return False

        for v in range(1, n + 1):
            if state[v] != 1:
                indeg_arr[v] = 0

        for v in range(1, n + 1):
            if state[v] == 1:
                continue

            for to in orig_out[v]:
                if state[to] != 1:
                    indeg_arr[to] += 1

        q = deque()
        rem_count = 0

        for v in range(1, n + 1):
            if state[v] != 1:
                rem_count += 1
                if indeg_arr[v] == 0:
                    q.append(v)

        done = 0

        while q:
            if not force and stop:
                return False

            v = q.popleft()
            done += 1

            for to in orig_out[v]:
                if state[to] != 1:
                    indeg_arr[to] -= 1
                    if indeg_arr[to] == 0:
                        q.append(to)

        return done == rem_count

    def output_all():
        sys.stdout.write(''.join(f'{v}\n' for v in range(1, n + 1)))
        sys.stdout.flush()

    def finalize_and_output():
        # if not have_valid_answer:
        #     output_all()
        #     return

        for v in range(1, n + 1):
            if state[v] == 0:
                state[v] = 1

        if not proverka(force=True):
            output_all()
            return

        ans = [v for v in range(1, n + 1) if state[v] == 1]

        if not ans:
            output_all()
            return
        # sys.stdout.write(f'{len(ans)}\n') #удалить
        sys.stdout.write(''.join(f'{v}\n' for v in ans))
        sys.stdout.flush()

    def improve_answer():
        if not have_valid_answer:
            return

        candidate_order = [v for v in range(1, n + 1) if state[v] == 1]
        candidate_order.sort(key=lambda v: orig_in_deg[v] * len(orig_out[v]))

        while not stop:
            changed = False

            for v in candidate_order:
                if stop:
                    break

                if state[v] != 1:
                    continue

                state[v] = 0

                if proverka(force=False):
                    state[v] = -1
                    changed = True
                else:
                    state[v] = 1

            if stop:
                break

            if not changed:
                break

    for v in range(1, n + 1):
        add_queue(v)

    shimaem_graf()

    if stop:
        finalize_and_output()
        return

    rebuild_heap()
    heap_ready = True

    while processed < n and not stop:
        shimaem_graf()

        if stop or processed >= n:
            break

        item = extract_heap()

        if item is None:
            for v in range(1, n + 1):
                if state[v] == 0:
                    udali(v, 1)
            break

        _, v = item
        udali(v, 1)

    if stop:
        finalize_and_output()
        return

    for v in range(1, n + 1):
        if state[v] == 0:
            udali(v, 1)

    if not proverka(force=True):
        finalize_and_output()
        return

    have_valid_answer = True

    improve_answer()

    finalize_and_output()


if __name__ == '__main__':
    main()