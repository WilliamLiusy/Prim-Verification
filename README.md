# Prim-Verification
证明来源：https://oi-wiki.org/graph/mst/

## 任务拆分
### Module Tree

定义树和环 （vertex, edge用list）

stateMonad 的 state：加入的边的list和点的list

不确定性：加点的时候边权最小如果有很多个，应当任选一个

不变式：永远有一个MST包含现在选到的所有边

cqx：List <-> Graph (vvalid, evalid)
List -> Graph: In v List -> vvalid v = True
可以沿用subgraph的定义

定义最小生成树

树的性质：要用

1、随便再加一条边会有且仅有一个环

2、树等价于n-1条边，连通


### Module Prim
定义Prim算法

要证明：

每一步生成都是树

每一步生成的被某一个MST包含