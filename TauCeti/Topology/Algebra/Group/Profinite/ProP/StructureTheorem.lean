/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ZMod
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CompactModule
import Mathlib.NumberTheory.Padics.ProperSpace
import TauCeti.Algebra.Group.Prod
import TauCeti.Algebra.Module.DiscreteValuationRing
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The structure theorem for topologically finitely generated abelian pro-`p` groups

A topologically finitely generated abelian pro-`p` group `A` is topologically isomorphic to
`ℤ_p ^ r × T`, where `T = ∏ i : Fin m, ℤ/p^(e i)` is a finite abelian `p`-group carrying the
discrete topology and every exponent `e i` is positive, so that the finite factor has no trivial
summand. The isomorphism is an isomorphism of topological groups. This is the abelian case of
the classification of finitely generated pro-`p` groups; it describes, for instance, the
abelianisation of any topologically finitely generated pro-`p` group.

The statement records only a topological group isomorphism, not a `ℤ_[p]`-linear equivalence
for the canonical `p`-adic exponentiation `TauCeti.IsProP.module`. (Every continuous
homomorphism between abelian pro-`p` groups commutes with `p`-adic exponentiation,
`TauCeti.IsProP.map_padicPow`, so no information is lost, but no linear equivalence is packaged
here.) The rank `r` and the exponents `e i`, up to reindexing, are invariants of `A`.
The identification of `T` with the torsion subgroup and the uniqueness results are proved in
`TauCeti.Topology.Algebra.Group.Profinite.ProP.Torsion`. In particular,
`TauCeti.exists_equiv_exponents_of_continuousMulEquiv_pi_padicInt_prod_pi_zmod` compares the
exponents in any two decompositions with positive exponents; its algebraic input is
`ZMod.exists_equiv_exponents_of_pi_pow_addEquiv`.

## Main result

* `TauCeti.IsProP.exists_continuousMulEquiv_pi_padicInt_prod_pi_zmod`: a topologically finitely
  generated abelian pro-`p` group is topologically isomorphic to
  `ℤ_p ^ r × ∏ i : Fin m, ℤ/p^(e i)`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 4.3.
-/

public section

namespace TauCeti.IsProP

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommGroup A] [TopologicalSpace A]
  [IsTopologicalGroup A] [CompactSpace A] [TotallyDisconnectedSpace A]

/-- **Structure theorem for topologically finitely generated abelian pro-`p` groups.** Such a
group is topologically isomorphic to `ℤ_p ^ r × ∏ i : Fin m, ℤ/p^(e i)` with every `e i`
positive, where the finite factor carries the discrete topology. -/
theorem exists_continuousMulEquiv_pi_padicInt_prod_pi_zmod (hA : IsProP p A)
    (hfg : IsTopologicallyFinitelyGenerated A) :
    ∃ (r m : ℕ) (e : Fin m → ℕ), (∀ i, 0 < e i) ∧
      Nonempty (A ≃ₜ* Multiplicative ((Fin r → ℤ_[p]) × ((i : Fin m) → ZMod (p ^ e i)))) := by
  let _ : Module ℤ_[p] (Additive A) := hA.module
  have _ : ContinuousSMul ℤ_[p] (Additive A) := hA.continuousSMul_module
  have _ : Module.Finite ℤ_[p] (Additive A) :=
    hA.isTopologicallyFinitelyGenerated_iff_module_finite.mp hfg
  obtain ⟨r, m, e, he, ⟨f⟩⟩ :=
    Module.equiv_pi_prod_pi_quotient_span_pow ℤ_[p] (Additive A) PadicInt.irreducible_p
  have _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let g : ((i : Fin m) → ℤ_[p] ⧸ ℤ_[p] ∙ (p : ℤ_[p]) ^ e i) ≃+ ((i : Fin m) → ZMod (p ^ e i)) :=
    AddEquiv.piCongrRight fun i ↦ (PadicInt.quotientSpanPowEquivZMod (e i)).toAddEquiv
  let ψ : Additive A ≃+ (Fin r → ℤ_[p]) × ((i : Fin m) → ZMod (p ^ e i)) :=
    f.toAddEquiv.trans ((AddEquiv.refl _).prodCongr g)
  -- The inverse of `ψ` is continuous: it is `ℤ_[p]`-linear on the free factor and the finite
  -- factor is discrete.
  have hψ : Continuous ψ.symm := by
    have h₁ : Continuous fun v : Fin r → ℤ_[p] ↦ f.symm (v, 0) :=
      (f.symm.toLinearMap ∘ₗ LinearMap.inl ℤ_[p] _ _).continuous_on_pi
    have h₂ : Continuous fun t : (i : Fin m) → ZMod (p ^ e i) ↦ f.symm (0, g.symm t) :=
      continuous_of_discreteTopology
    refine ((h₁.comp continuous_fst).add (h₂.comp continuous_snd)).congr fun x ↦ ?_
    simp only [Pi.add_apply, Function.comp_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
    simp [ψ, AddEquiv.prodCongr_symm, AddEquiv.prodCongr_apply]
  let e' : A ≃* Multiplicative ((Fin r → ℤ_[p]) × ((i : Fin m) → ZMod (p ^ e i))) :=
    AddEquiv.toMultiplicativeRight ψ
  have he' : Continuous e'.symm := continuous_toMul.comp (hψ.comp continuous_toAdd)
  exact ⟨r, m, e, he, ⟨ContinuousMulEquiv.mk e'
    (he'.continuous_symm_of_equiv_compact_to_t2 (f := e'.symm.toEquiv)) he'⟩⟩

end TauCeti.IsProP
