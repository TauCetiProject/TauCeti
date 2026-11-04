/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import TauCeti.RepresentationTheory.LinHom.EndTensor
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality

/-!
# Equivariant Clifford modules and invariant Clifford tensors

Let `Q` be a quadratic form on a finitely generated projective `R`-module `V`, and let
`π : CliffordAlgebra Q → End_A E` make a finitely generated projective `A`-module `E` a Clifford
module, with Clifford multiplication `c(v) = π (ι Q v)`. Suppose a group `G` acts on `V` by
isometries of `Q`, through `ρ`, and on `E` through `μ`. Each `ρ g` then induces an algebra
automorphism `CliffordAlgebra.map (ρ g)` of the Clifford algebra.

By `TauCeti.endValuedTensorEquiv_mem_invariants_iff`, Clifford multiplication is a fixed tensor
in `(A ⊗[R] V)* ⊗ (E* ⊗ E)` exactly when it satisfies the intertwining equation
`c(ρ g v) = μ g ∘ c(v) ∘ μ g⁻¹`. Since the vectors generate the Clifford algebra, this equation on
generators is equivalent to the same equation for the whole algebra action,

  `π (map (ρ g) a) = μ g ∘ π a ∘ μ g⁻¹`,

which is what lets the algebra action of `Cl(V)` on `E` descend to the associated bundles
`P ×_G Cl(V)` and `P ×_G E` of a principal `G`-bundle `P`.

## Main results

* `CliffordAlgebra.endValuedTensorEquiv_ι_mem_invariants_iff`: the tensor of Clifford
  multiplication is invariant if and only if the Clifford algebra action intertwines the induced
  automorphisms `map (ρ g)` with conjugation by `μ g`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter II §3.
-/

public section

namespace CliffordAlgebra

open TauCeti

variable {R A V E G : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V]
  [AddCommGroup E] [Module A E] [Module.Finite A E] [Module.Projective A E]
  [Module R E] [IsScalarTower R A E] [Group G]
  {Q : QuadraticForm R V} (ρ : Representation R G V) (hρ : ∀ g v, Q (ρ g v) = Q v)
  (μ : Representation A G E) (π : CliffordAlgebra Q →ₐ[R] Module.End A E)

/-- **Clifford multiplication is an invariant tensor exactly when the Clifford action is
equivariant.** For a group acting on `V` by isometries `ρ g` of `Q` and on a Clifford module `E`
by `μ`, the tensor of Clifford multiplication `v ↦ π (ι Q v)` is fixed by the tensor product
representation `(ρ_A)* ⊗ (μ* ⊗ μ)` if and only if `π (map (ρ g) a) = μ g ∘ π a ∘ μ g⁻¹` for every
group element `g` and every Clifford element `a`. -/
theorem endValuedTensorEquiv_ι_mem_invariants_iff :
    endValuedTensorEquiv R A V E (π.toLinearMap ∘ₗ ι Q) ∈
        ((ρ.baseChange A).dual.tprod (μ.dual.tprod μ)).invariants ↔
      ∀ g a, π (map ⟨ρ g, hρ g⟩ a) = μ g ∘ₗ π a ∘ₗ μ g⁻¹ := by
  rw [endValuedTensorEquiv_mem_invariants_iff]
  refine ⟨fun h g a ↦ ?_, fun h g v ↦ ?_⟩
  · -- The intertwining equation on generators, in the form `μ g ∘ c(m) = c(ρ g m) ∘ μ g`,
    -- extends to the whole Clifford algebra.
    have hU (m : V) : μ g ∘ₗ π (ι Q m) = π (ι Q (ρ g m)) ∘ₗ μ g := by
      ext x
      simpa using congr($(h g m) (μ g x)).symm
    have ha := comp_eq_map_comp_of_forall_ι (f := ⟨ρ g, hρ g⟩) hU a
    ext x
    simpa using congr($ha (μ g⁻¹ x)).symm
  · -- The isometry `⟨ρ g, hρ g⟩` applied to `v` is `ρ g v` by definition of its coercion.
    have hv := h g (ι Q v)
    rwa [map_apply_ι] at hv

end CliffordAlgebra
