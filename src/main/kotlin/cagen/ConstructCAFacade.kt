package cagen

object ConstructCAFacade {
    fun construct(composited: System): UseContract {
        // A list of non overlapping use contracts.
        val instantiated = composited.signature.instances
            .mapIndexed { idx, it ->
                val c = (it.type as SystemType).system.contracts.first()
                c.prefix(it.name + "_$idx")
            }

        val megaSubst = instantiated.map { (a, b) -> b }.flatten()
        val product = instantiated.map { (a, b) -> a }
            .reduce { a, b -> a * b }
        return UseContract(product, megaSubst.toMutableList())
    }
}
