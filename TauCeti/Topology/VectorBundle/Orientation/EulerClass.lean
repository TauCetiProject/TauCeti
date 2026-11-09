/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Orientation.PositiveSection

/-!
# The Euler class of an oriented vector bundle

Let `E → B` be a real vector bundle with model fibre `F` of dimension `n + 1`, and let `o` be an
orientation of `E`. The *Euler class* `e(E, o) ∈ Hⁿ⁺¹(B; ℤ)`
(`TauCeti.VectorBundleOrientation.eulerClass`) is the pull-back along the zero section of the image
in `Hⁿ⁺¹(E; ℤ)` of the Thom class `U ∈ Hⁿ⁺¹(E, E₀; ℤ)` of the oriented bundle
(`TauCeti.VectorBundleOrientation.thomClass`): it is the value at `U` of the Euler class map
`TauCeti.eulerClass : Hⁿ⁺¹(E, E₀) ⟶ Hⁿ⁺¹(B)` (`TauCeti.VectorBundleOrientation.eulerClass_def`).

Its basic laws follow from those of the Thom class.

* It is natural under pullback of bundles: the Euler class of `f*E`, with the pulled-back
  orientation, is the pull-back along `f` of the Euler class of `E`
  (`TauCeti.VectorBundleOrientation.eulerClass_pullback`).
* Reversing the orientation negates it (`TauCeti.VectorBundleOrientation.eulerClass_neg`).
* In odd rank it is `2`-torsion (`TauCeti.VectorBundleOrientation.two_smul_eulerClass`). The
  fibrewise antipodal map `v ↦ -v` fixes the zero section, so it does not change Euler classes,
  and in odd rank it reverses the orientation of every fibre, so it carries the Thom class to the
  Thom class of the opposite orientation. Hence `e(E, o) = e(E, -o) = -e(E, o)`. The class need not
  vanish integrally.
* It vanishes when the bundle has a nowhere-zero continuous section
  (`TauCeti.VectorBundleOrientation.eulerClass_eq_zero_of_forall_ne_zero`).
* In rank one it vanishes over a normal paracompact base
  (`TauCeti.VectorBundleOrientation.eulerClass_eq_zero_of_finrank_eq_one`): an oriented line
  bundle has a positive, hence nowhere-zero, continuous section
  (`TauCeti.VectorBundleOrientation.exists_continuous_section_ne_zero`). Since one is odd, this
  strengthens `2 • e(E, o) = 0` to `e(E, o) = 0`.

Integral coefficients are `ULift ℤ`, as for the Thom class.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9, Property 9.1 (naturality), Property 9.4 (orientation reversal),
  Property 9.5 (`2e = 0` in odd rank) and Property 9.7 (a nowhere-zero section kills `e`).
-/

public section

noncomputable section

open Bundle CategoryTheory Module

universe w

namespace TauCeti.VectorBundleOrientation

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {n : ℕ} (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1)

/-- **The Euler class of an oriented vector bundle.** For an orientation `o` of a real vector
bundle `E → B` with model fibre `F` of dimension `n + 1`, this is the class `e(E, o) ∈ Hⁿ⁺¹(B; ℤ)`
obtained from the Thom class `U ∈ Hⁿ⁺¹(E, E₀; ℤ)` by restriction to `Hⁿ⁺¹(E; ℤ)` followed by
pull-back along the zero section. -/
def eulerClass :
    (TopCat.of B).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :=
  TauCeti.eulerClass (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) F E (n + 1)
    (o.thomClass hF)

/-- The Euler class of an oriented bundle is the value of the Euler class map
`TauCeti.eulerClass : Hⁿ⁺¹(E, E₀) ⟶ Hⁿ⁺¹(B)` at its Thom class. -/
theorem eulerClass_def :
    o.eulerClass hF = TauCeti.eulerClass (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) F E (n + 1) (o.thomClass hF) :=
  (rfl)

/-- **Reversing the orientation negates the Euler class.** -/
@[simp]
theorem eulerClass_neg : (-o).eulerClass hF = -o.eulerClass hF := by
  rw [eulerClass_def, eulerClass_def, thomClass_neg, map_neg]

/-- **Naturality of the Euler class.** The Euler class of the pullback `f*E` of an oriented bundle
along a continuous map `f : B' → B`, with the pulled-back orientation, is the pull-back along `f`
of the Euler class of `E`. -/
theorem eulerClass_pullback {B' : Type w} [TopologicalSpace B'] (f : C(B', B)) :
    (o.pullback f).eulerClass hF =
      TopCat.singularCohomologyMap (TopCat.ofHom f) (n + 1) (o.eulerClass hF) := by
  rw [eulerClass_def, eulerClass_def, ← singularCohomologyMap_pullbackThomPairMap_thomClass]
  -- Term-mode step: the zero of the fibres of `f*E` enters the two sides through instances that
  -- agree only up to unfolding, so `rw [← ConcreteCategory.comp_apply]` cannot match.
  exact ConcreteCategory.congr_hom (TauCeti.eulerClass_pullback F E f (n + 1)) (o.thomClass hF)

/-- In odd rank `n + 1`, the opposite orientation has the same Euler class: the antipodal map
`v ↦ -v` fixes the zero section and carries the Thom class to that of the opposite orientation. -/
theorem eulerClass_neg_eq_of_even (hn : Even n) : (-o).eulerClass hF = o.eulerClass hF := by
  rw [eulerClass_def, eulerClass_def, ← singularCohomologyMap_negThomPairMap_thomClass o hF hn,
    ← ConcreteCategory.comp_apply, singularCohomologyMap_negThomPairMap_comp_eulerClass]

/-- **In odd rank the Euler class is `2`-torsion**: for an oriented bundle of rank `n + 1` with `n`
even, `2 • e(E, o) = 0`. -/
theorem two_smul_eulerClass (hn : Even n) : 2 • o.eulerClass hF = 0 := by
  have h := o.eulerClass_neg_eq_of_even hF hn
  rw [eulerClass_neg, neg_eq_iff_add_eq_zero] at h
  rw [two_smul, h]

/-- **A nowhere-vanishing section kills the Euler class.** If an oriented real vector bundle has a
continuous section `s` with `s b ≠ 0` for every `b`, its Euler class vanishes. -/
theorem eulerClass_eq_zero_of_forall_ne_zero {s : ∀ b, E b}
    (hs : Continuous fun b ↦ TotalSpace.mk' F b (s b)) (hs₀ : ∀ b, s b ≠ 0) :
    o.eulerClass hF = 0 := by
  rw [eulerClass_def, TauCeti.eulerClass_eq_zero_of_forall_ne_zero F E hs hs₀]
  simp

section LineBundle

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **The Euler class of an oriented line bundle vanishes.** For an oriented real vector bundle of
rank one over a normal paracompact base, `e(E, o) = 0` in `H¹(B; ℤ)`: the bundle has a positive,
hence nowhere-zero, continuous section. -/
theorem eulerClass_eq_zero_of_finrank_eq_one [NormalSpace B] [ParacompactSpace B]
    (o : VectorBundleOrientation F E (Fin 1)) (hF : finrank ℝ F = 1) : o.eulerClass hF = 0 := by
  obtain ⟨s, hs, hs₀⟩ := o.exists_continuous_section_ne_zero (by rw [hF, Fintype.card_fin])
  exact o.eulerClass_eq_zero_of_forall_ne_zero hF hs hs₀

end LineBundle

end TauCeti.VectorBundleOrientation
