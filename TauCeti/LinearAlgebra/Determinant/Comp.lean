/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Exact
public import TauCeti.LinearAlgebra.Exact
public import TauCeti.RingTheory.Finiteness.Finsupp
import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# The determinant line of a composition

For linear maps `f : M → N` and `g : N → P` between vector spaces whose kernels and cokernels
are finite-dimensional, the kernels and cokernels of `f`, `g` and `g ∘ f` form the exact sequence

`0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0`

(`LinearMap.kerCompToKer`, `LinearMap.kerToCoker`, `LinearMap.cokerToCokerComp`, with the
inclusion of kernels first and the quotient map of cokernels last). Its alternating sum of
dimensions is the additivity of the index under composition (`LinearMap.index_comp`). Its
determinant lines give the finer, canonical statement

`det (g ∘ f) ≃ det f ⊗ det g`

for the determinant lines `det f = det (ker f) ⊗ (det (coker f))^*` (`LinearMap.detLine`), with no
choice of bases or complements (`LinearMap.detLineCompEquiv`). This is
`TauCeti.detLineSixTermEquiv` for that sequence.

For Fredholm operators this is the composition law of determinant lines: orientations of the
determinant lines of `f` and `g` orient the determinant line of `g ∘ f`, for instance when an
operator is composed with a change of trivialization.

The composition law is natural: for isomorphisms of the three spaces commuting with the maps, it
intertwines the transports of determinant lines along the commuting squares
(`LinearMap.detLineCompEquiv_detLineCongr`). So the identification of `det (g ∘ f)` with
`det f ⊗ det g` does not depend on the trivializations in which `f` and `g` are written. This
follows from the naturality of the six-term isomorphism (`TauCeti.detLineSixTermEquiv_congr`),
since the isomorphisms induced on kernels and cokernels commute with the maps of the
kernel–cokernel sequences.

The composition law is unital: when one factor is bijective, its determinant line is trivialized
(`LinearMap.detLineEquivOfBijective`), and against this trivialization the composition law is the
transport of determinant lines along the bijective factor, read as an isomorphism of the sources
or of the targets (`LinearMap.detLineCompEquiv_apply_of_bijective_left`,
`LinearMap.detLineCompEquiv_apply_of_bijective_right`). The kernel–cokernel sequence then
collapses to isomorphisms `ker (g ∘ f) ≃ ker g` and `coker (g ∘ f) ≃ coker g` (or `ker (g ∘ f) =
ker f` and `coker f ≃ coker (g ∘ f)`), and no sign appears.

## Main declarations

* `LinearMap.detLineCompEquiv`: the isomorphism `det (g ∘ f) ≃ det f ⊗ det g`.
* `LinearMap.detLineCompEquiv_def`: it is the six-term isomorphism of that sequence.
* `LinearMap.detLineCompEquiv_tmul`: its value on exterior products.
* `LinearMap.detLineCompEquiv_detLineCongr`: its naturality for isomorphisms of the three spaces.
* `LinearMap.detLineCompEquiv_apply_of_bijective_left`,
  `LinearMap.detLineCompEquiv_apply_of_bijective_right`: the unit laws, for a bijective first or
  second factor.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties,
  and classification*, Math. Scand. **118** (2016), 203–268, arXiv:1304.6368.
-/

public section

noncomputable section

open Module TensorProduct

namespace LinearMap

variable {K : Type*} [Field K] {M N P : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
  [Module K N] [AddCommGroup P] [Module K P] (f : M →ₗ[K] N) (g : N →ₗ[K] P)
  [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)]
  [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (P ⧸ range g)]

/-- **The determinant line of a composition.** For linear maps `f : M → N` and `g : N → P` with
finite-dimensional kernels and cokernels, the canonical isomorphism
`det (g ∘ f) ≃ det f ⊗ det g` of determinant lines. It is `TauCeti.detLineSixTermEquiv` for the
exact sequence `0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0`; its value
on exterior products is `LinearMap.detLineCompEquiv_tmul`. -/
def detLineCompEquiv : (g ∘ₗ f).detLine ≃ₗ[K] f.detLine ⊗[K] g.detLine :=
  have : FiniteDimensional K (P ⧸ range (g ∘ₗ f)) := Module.Finite.quotient_range_comp f g
  TauCeti.detLineSixTermEquiv (Submodule.inclusion_injective (ker_le_ker_comp f g))
    (f.exact_inclusion_kerCompToKer g) (f.exact_kerCompToKer_kerToCoker g)
    (f.exact_kerToCoker_cokerToCokerComp g) (f.exact_cokerToCokerComp_factor g)
    (Submodule.factor_surjective _)

/-- `LinearMap.detLineCompEquiv` is the six-term isomorphism `TauCeti.detLineSixTermEquiv` of the
exact sequence `0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0`. -/
theorem detLineCompEquiv_def [FiniteDimensional K (P ⧸ range (g ∘ₗ f))] :
    f.detLineCompEquiv g = TauCeti.detLineSixTermEquiv
      (Submodule.inclusion_injective (ker_le_ker_comp f g)) (f.exact_inclusion_kerCompToKer g)
      (f.exact_kerCompToKer_kerToCoker g) (f.exact_kerToCoker_cokerToCokerComp g)
      (f.exact_cokerToCokerComp_factor g) (Submodule.factor_surjective _) :=
  (rfl)

/-- **The value of `LinearMap.detLineCompEquiv` on exterior products.** Choose `u`, a family of
`dim (ker f)` vectors of `ker f`, and families `v`, `w`, `x` and `y` in `ker (g ∘ f)`, `ker g`,
`coker f` and `coker (g ∘ f)` whose images complete them along the exact sequence
`0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0`. Let `β`, `γ`, `δ` and
`ε` be the exterior products in `ker (g ∘ f)`, `ker g`, `coker f` and `coker (g ∘ f)` of the
images of `u`, `v`, `w` and `x` followed by `v`, `w`, `x` and `y`. If `ψ` takes the value `1` at
`δ` and `χ` takes the value `1` at the exterior product of the classes of `y` in `coker g`, then
`β ⊗ φ` goes to `φ ε • ((α ⊗ ψ) ⊗ (γ ⊗ χ))`, with `α` the exterior product of `u`. -/
theorem detLineCompEquiv_tmul (u : Fin (finrank K (ker f)) → ker f)
    (v : Fin (finrank K (range (f.kerCompToKer g))) → ker (g ∘ₗ f))
    (w : Fin (finrank K (range (f.kerToCoker g))) → ker g)
    (x : Fin (finrank K (range (f.cokerToCokerComp g))) → N ⧸ range f)
    (y : Fin (finrank K (P ⧸ range g)) → P ⧸ range (g ∘ₗ f))
    {β : TauCeti.detLine K (ker (g ∘ₗ f))} (hβ : (β : ExteriorAlgebra K (ker (g ∘ₗ f))) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ u) v))
    {γ : TauCeti.detLine K (ker g)} (hγ : (γ : ExteriorAlgebra K (ker g)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerCompToKer g ∘ v) w))
    {δ : TauCeti.detLine K (N ⧸ range f)} (hδ : (δ : ExteriorAlgebra K (N ⧸ range f)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerToCoker g ∘ w) x))
    {ε : TauCeti.detLine K (P ⧸ range (g ∘ₗ f))}
    (hε : (ε : ExteriorAlgebra K (P ⧸ range (g ∘ₗ f))) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.cokerToCokerComp g ∘ x) y))
    (φ : Dual K (TauCeti.detLine K (P ⧸ range (g ∘ₗ f))))
    {ψ : Dual K (TauCeti.detLine K (N ⧸ range f))} (hψ : ψ δ = 1)
    {χ : Dual K (TauCeti.detLine K (P ⧸ range g))}
    (hχ : χ (exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range f g) ∘ y)) = 1) :
    f.detLineCompEquiv g (β ⊗ₜ φ) = φ ε • ((exteriorPower.ιMulti K _ u ⊗ₜ ψ) ⊗ₜ (γ ⊗ₜ χ)) :=
  have : FiniteDimensional K (P ⧸ range (g ∘ₗ f)) := Module.Finite.quotient_range_comp f g
  TauCeti.detLineSixTermEquiv_tmul _ _ _ _ _ _ u v w x y hβ hγ hδ hε φ hψ hχ

section Naturality

variable {M' N' P' : Type*} [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N']
  [AddCommGroup P'] [Module K P'] {f' : M' →ₗ[K] N'} {g' : N' →ₗ[K] P'}
  [FiniteDimensional K (ker f')] [FiniteDimensional K (ker g')]
  [FiniteDimensional K (N' ⧸ range f')] [FiniteDimensional K (P' ⧸ range g')]
  (eM : M ≃ₗ[K] M') (eN : N ≃ₗ[K] N') (eP : P ≃ₗ[K] P')

/-- **Naturality of the composition law of determinant lines.** Let `f' ∘ eM = eN ∘ f` and
`g' ∘ eN = eP ∘ g` be commuting squares with `eM`, `eN` and `eP` linear isomorphisms. Then the
isomorphisms `det (g ∘ f) ≃ det f ⊗ det g` and `det (g' ∘ f') ≃ det f' ⊗ det g'`
(`LinearMap.detLineCompEquiv`) are intertwined by the transports of determinant lines along the
squares (`LinearMap.detLineCongr`): along the pasted square `(g' ∘ f') ∘ eM = eP ∘ (g ∘ f)` on
the left, and along the two squares on the right. For instance, the composition law of operators
expressed in two trivializations of the bundles involved gives the same identification of
determinant lines. -/
theorem detLineCompEquiv_detLineCongr (hf : f' ∘ₗ eM.toLinearMap = eN.toLinearMap ∘ₗ f)
    (hg : g' ∘ₗ eN.toLinearMap = eP.toLinearMap ∘ₗ g) (x : (g ∘ₗ f).detLine) :
    f'.detLineCompEquiv g' ((g ∘ₗ f).detLineCongr eM eP
        (by rw [comp_assoc, hf, ← comp_assoc, hg, comp_assoc]) x) =
      TensorProduct.congr (f.detLineCongr eM eN hf) (g.detLineCongr eN eP hg)
        (f.detLineCompEquiv g x) := by
  have : FiniteDimensional K (P ⧸ range (g ∘ₗ f)) := Module.Finite.quotient_range_comp f g
  have : FiniteDimensional K (P' ⧸ range (g' ∘ₗ f')) := Module.Finite.quotient_range_comp f' g'
  have hgf : (g' ∘ₗ f') ∘ₗ eM.toLinearMap = eP.toLinearMap ∘ₗ (g ∘ₗ f) := by
    rw [comp_assoc, hf, ← comp_assoc, hg, comp_assoc]
  -- The six isomorphisms of the kernel–cokernel sequences, as in `LinearMap.detLineCongr`.
  let e₁ := eM.ofSubmodules _ _ (f.map_ker_eq_ker_of_comp_eq eM.surjective eN.injective hf)
  let e₂ := eM.ofSubmodules _ _
    ((g ∘ₗ f).map_ker_eq_ker_of_comp_eq eM.surjective eP.injective hgf)
  let e₃ := eN.ofSubmodules _ _ (g.map_ker_eq_ker_of_comp_eq eN.surjective eP.injective hg)
  let e₄ := Submodule.Quotient.equiv _ _ eN (f.map_range_eq_range_of_comp_eq eM.surjective hf)
  let e₅ := Submodule.Quotient.equiv _ _ eP
    ((g ∘ₗ f).map_range_eq_range_of_comp_eq eM.surjective hgf)
  let e₆ := Submodule.Quotient.equiv _ _ eP (g.map_range_eq_range_of_comp_eq eN.surjective hg)
  -- They commute with the maps of the two sequences.
  have h₁ : Submodule.inclusion (ker_le_ker_comp f' g') ∘ₗ e₁.toLinearMap =
      e₂.toLinearMap ∘ₗ Submodule.inclusion (ker_le_ker_comp f g) := by
    ext
    simp [e₁, e₂, LinearEquiv.ofSubmodules_apply]
  have h₂ : f'.kerCompToKer g' ∘ₗ e₂.toLinearMap = e₃.toLinearMap ∘ₗ f.kerCompToKer g := by
    ext z
    simp only [e₂, e₃, comp_apply, LinearEquiv.coe_coe, coe_kerCompToKer_apply,
      LinearEquiv.ofSubmodules_apply]
    exact LinearMap.congr_fun hf (z : M)
  have h₃ : f'.kerToCoker g' ∘ₗ e₃.toLinearMap = e₄.toLinearMap ∘ₗ f.kerToCoker g := by
    ext
    simp [e₃, e₄, kerToCoker_apply]
  have h₄ : f'.cokerToCokerComp g' ∘ₗ e₄.toLinearMap =
      e₅.toLinearMap ∘ₗ f.cokerToCokerComp g := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y ↦ ?_)
    simp only [e₄, e₅, comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe,
      Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, cokerToCokerComp_mk]
    exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun hg y)
  have h₅ : Submodule.factor (range_comp_le_range f' g') ∘ₗ e₅.toLinearMap =
      e₆.toLinearMap ∘ₗ Submodule.factor (range_comp_le_range f g) := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y ↦ ?_)
    simp [e₅, e₆]
  -- Written through these isomorphisms, the three transports are those of
  -- `TauCeti.detLineSixTermEquiv_congr`, and `LinearMap.detLineCompEquiv` is by definition the
  -- six-term isomorphism (`LinearMap.detLineCompEquiv_def`).
  rw [detLineCompEquiv_def f g, detLineCompEquiv_def f' g']
  simp only [detLineCongr_eq_congr]
  exact TauCeti.detLineSixTermEquiv_congr (Submodule.inclusion_injective (ker_le_ker_comp f g))
    (f.exact_inclusion_kerCompToKer g) (f.exact_kerCompToKer_kerToCoker g)
    (f.exact_kerToCoker_cokerToCokerComp g) (f.exact_cokerToCokerComp_factor g)
    (Submodule.factor_surjective _) (Submodule.inclusion_injective (ker_le_ker_comp f' g'))
    (f'.exact_inclusion_kerCompToKer g') (f'.exact_kerCompToKer_kerToCoker g')
    (f'.exact_kerToCoker_cokerToCokerComp g') (f'.exact_cokerToCokerComp_factor g')
    (Submodule.factor_surjective _) e₁ e₂ e₃ e₄ e₅ e₆ h₁ h₂ h₃ h₄ h₅ x

end Naturality

section Bijective

/-! ### Unit laws -/

/-- `LinearMap.detLineCompEquiv_apply_of_bijective_left` on `β ⊗ φ`, for the data with which
`LinearMap.detLineCompEquiv_tmul` evaluates the composition law. -/
private theorem detLineCompEquiv_tmul_of_bijective_left (hf : Function.Bijective f)
    (v : Fin (finrank K (range (f.kerCompToKer g))) → ker (g ∘ₗ f))
    (w : Fin (finrank K (range (f.kerToCoker g))) → ker g)
    (x : Fin (finrank K (range (f.cokerToCokerComp g))) → N ⧸ range f)
    (y : Fin (finrank K (P ⧸ range g)) → P ⧸ range (g ∘ₗ f))
    {β : TauCeti.detLine K (ker (g ∘ₗ f))} (hβ : (β : ExteriorAlgebra K (ker (g ∘ₗ f))) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) v))
    {γ : TauCeti.detLine K (ker g)} (hγ : (γ : ExteriorAlgebra K (ker g)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerCompToKer g ∘ v) w))
    {δ : TauCeti.detLine K (N ⧸ range f)} (hδ : (δ : ExteriorAlgebra K (N ⧸ range f)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerToCoker g ∘ w) x))
    {ε : TauCeti.detLine K (P ⧸ range (g ∘ₗ f))}
    (hε : (ε : ExteriorAlgebra K (P ⧸ range (g ∘ₗ f))) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.cokerToCokerComp g ∘ x) y))
    (φ : Dual K (TauCeti.detLine K (P ⧸ range (g ∘ₗ f))))
    {ψ : Dual K (TauCeti.detLine K (N ⧸ range f))} (hψ : ψ δ = 1)
    {χ : Dual K (TauCeti.detLine K (P ⧸ range g))}
    (hχ : χ (exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range f g) ∘ y)) = 1) :
    f.detLineCompEquiv g (β ⊗ₜ φ) = (f.detLineEquivOfBijective hf).symm 1 ⊗ₜ
      (g ∘ₗ f).detLineCongr (LinearEquiv.ofBijective f hf) (LinearEquiv.refl K P)
        (by ext; simp) (β ⊗ₜ φ) := by
  -- The families in `ker f`, in `coker f` and in its subspace `range (kerToCoker f g)` are empty.
  have hker := finrank_ker_eq_zero_of_injective hf.1
  have hcoker := finrank_quotient_range_eq_zero_of_surjective hf.2
  have h₃ : finrank K (range (f.kerToCoker g)) = 0 :=
    Nat.eq_zero_of_le_zero (hcoker ▸ Submodule.finrank_le _)
  have h₄ : finrank K (range (f.cokerToCokerComp g)) = 0 :=
    Nat.eq_zero_of_le_zero (hcoker ▸ finrank_range_le _)
  -- The unit of `det f` is the empty product tensored with `ψ`, normalized at the empty `δ`.
  have hunit : (f.detLineEquivOfBijective hf).symm 1 =
      exteriorPower.ιMulti K _ (Module.finBasis K (ker f)) ⊗ₜ ψ := by
    refine detLineEquivOfBijective_symm_one hf _ ψ 0 ?_
    convert hψ using 2
    refine Subtype.ext ?_
    rw [hδ, exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_of_eq_zero hcoker,
      TauCeti.ExteriorAlgebra.ιMulti_of_eq_zero (by rw [h₃, h₄])]
  -- On kernels, `f` carries `β` to `γ`.
  have hK : ∀ e : ker (g ∘ₗ f) ≃ₗ[K] ker g, (∀ z, (e z : N) = f z) →
      LinearEquiv.detLineCongr e β = γ := by
    intro e he
    have hv : ⇑e.toLinearMap ∘ v = f.kerCompToKer g ∘ v :=
      funext fun i ↦ Subtype.ext (by simp [he])
    refine Subtype.ext ?_
    rw [LinearEquiv.coe_detLineCongr, hβ, ExteriorAlgebra.map_apply_ιMulti,
      TauCeti.ExteriorAlgebra.ιMulti_comp_append, TauCeti.ExteriorAlgebra.ιMulti_of_eq_zero hker,
      one_mul, hv, hγ, TauCeti.ExteriorAlgebra.ιMulti_append_of_eq_zero_right h₃]
  -- On cokernels, the identity of `P` carries `ε` to the exterior product at which `χ` is
  -- normalized, so that the transported functional is `φ ε • χ`.
  have hC : ∀ e : (P ⧸ range (g ∘ₗ f)) ≃ₗ[K] (P ⧸ range g),
      (∀ p : P, e (Submodule.Quotient.mk p) = Submodule.Quotient.mk p) →
        φ ∘ₗ (LinearEquiv.detLineCongr e).symm.toLinearMap = φ ε • χ := by
    intro e he
    have hy : ⇑e.toLinearMap ∘ y = Submodule.factor (range_comp_le_range f g) ∘ y := by
      funext i
      obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _ (y i)
      simp [← hp, he]
    have hε' : LinearEquiv.detLineCongr e ε =
        exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range f g) ∘ y) := by
      refine Subtype.ext ?_
      rw [LinearEquiv.coe_detLineCongr, hε, ExteriorAlgebra.map_apply_ιMulti,
        TauCeti.ExteriorAlgebra.ιMulti_comp_append, TauCeti.ExteriorAlgebra.ιMulti_of_eq_zero h₄,
        one_mul, hy, exteriorPower.ιMulti_apply_coe]
    rw [← Module.Invertible.dual_apply_smul_eq_self hχ (φ ∘ₗ _), ← hε', LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [detLineCompEquiv_tmul f g (Module.finBasis K (ker f)) v w x y hβ hγ hδ hε φ hψ hχ,
    detLineCongr_tmul, hK, hC, hunit, TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  · exact fun _ ↦ rfl
  · exact fun _ ↦ rfl

/-- **The composition law against a bijective first factor.** If `f` is bijective, its
determinant line is trivialized by `LinearMap.detLineEquivOfBijective`, and the composition law
`det (g ∘ f) ≃ det f ⊗ det g` (`LinearMap.detLineCompEquiv`) sends `x` to the unit of `det f`
tensored with the transport of `x` along the commuting square `g ∘ f = id ∘ (g ∘ f)`, in which
`f` is read as an isomorphism of the sources (`LinearMap.detLineCongr`). So precomposing with an
isomorphism identifies determinant lines exactly as the transport does, without a sign. -/
theorem detLineCompEquiv_apply_of_bijective_left (hf : Function.Bijective f)
    (x : (g ∘ₗ f).detLine) :
    f.detLineCompEquiv g x = (f.detLineEquivOfBijective hf).symm 1 ⊗ₜ
      (g ∘ₗ f).detLineCongr (LinearEquiv.ofBijective f hf) (LinearEquiv.refl K P)
        (by ext; simp) x := by
  have : FiniteDimensional K (P ⧸ range (g ∘ₗ f)) := Module.Finite.quotient_range_comp f g
  obtain ⟨v, w, x₀, y, β, γ, δ, ε, ψ, χ, hβ, hγ, hδ, hε, hψ, hχ, hspan⟩ :=
    TauCeti.exists_spanning_ιMulti_append_sixTerm
      (Submodule.inclusion_injective (ker_le_ker_comp f g)) (f.exact_inclusion_kerCompToKer g)
      (f.exact_kerCompToKer_kerToCoker g) (f.exact_kerToCoker_cokerToCokerComp g)
      (f.exact_cokerToCokerComp_factor g) (Submodule.factor_surjective _)
  -- Both sides are linear in `x`, and `det (ker (g ∘ f))` is spanned by `β`.
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', TensorProduct.tmul_add]
  | tmul z φ =>
    obtain ⟨r, rfl⟩ := hspan z
    rw [← TensorProduct.smul_tmul', map_smul, map_smul, TensorProduct.tmul_smul,
      detLineCompEquiv_tmul_of_bijective_left f g hf v w x₀ y hβ hγ hδ hε φ hψ hχ]

/-- `LinearMap.detLineCompEquiv_apply_of_bijective_right` on `β ⊗ φ`, for the data with which
`LinearMap.detLineCompEquiv_tmul` evaluates the composition law. -/
private theorem detLineCompEquiv_tmul_of_bijective_right (hg : Function.Bijective g)
    (v : Fin (finrank K (range (f.kerCompToKer g))) → ker (g ∘ₗ f))
    (w : Fin (finrank K (range (f.kerToCoker g))) → ker g)
    (x : Fin (finrank K (range (f.cokerToCokerComp g))) → N ⧸ range f)
    (y : Fin (finrank K (P ⧸ range g)) → P ⧸ range (g ∘ₗ f))
    {β : TauCeti.detLine K (ker (g ∘ₗ f))} (hβ : (β : ExteriorAlgebra K (ker (g ∘ₗ f))) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) v))
    {γ : TauCeti.detLine K (ker g)} (hγ : (γ : ExteriorAlgebra K (ker g)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerCompToKer g ∘ v) w))
    {δ : TauCeti.detLine K (N ⧸ range f)} (hδ : (δ : ExteriorAlgebra K (N ⧸ range f)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerToCoker g ∘ w) x))
    {ε : TauCeti.detLine K (P ⧸ range (g ∘ₗ f))}
    (hε : (ε : ExteriorAlgebra K (P ⧸ range (g ∘ₗ f))) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.cokerToCokerComp g ∘ x) y))
    (φ : Dual K (TauCeti.detLine K (P ⧸ range (g ∘ₗ f))))
    {ψ : Dual K (TauCeti.detLine K (N ⧸ range f))} (hψ : ψ δ = 1)
    {χ : Dual K (TauCeti.detLine K (P ⧸ range g))}
    (hχ : χ (exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range f g) ∘ y)) = 1) :
    f.detLineCompEquiv g (β ⊗ₜ φ) =
      (g ∘ₗ f).detLineCongr (LinearEquiv.refl K M) (LinearEquiv.ofBijective g hg).symm
          (by ext; simp) (β ⊗ₜ φ) ⊗ₜ (g.detLineEquivOfBijective hg).symm 1 := by
  -- The families in `ker g`, in `coker g` and in the subspace `range (kerCompToKer f g)` are
  -- empty.
  have hker := finrank_ker_eq_zero_of_injective hg.1
  have hcoker := finrank_quotient_range_eq_zero_of_surjective hg.2
  have h₂ : finrank K (range (f.kerCompToKer g)) = 0 :=
    Nat.eq_zero_of_le_zero (hker ▸ Submodule.finrank_le _)
  have h₃ : finrank K (range (f.kerToCoker g)) = 0 :=
    Nat.eq_zero_of_le_zero (hker ▸ finrank_range_le _)
  -- The unit of `det g` is the empty `γ` tensored with `χ`, normalized at the empty product.
  have hunit : (g.detLineEquivOfBijective hg).symm 1 = γ ⊗ₜ χ := by
    rw [detLineEquivOfBijective_symm_one hg 0 χ _ hχ]
    congr 1
    refine Subtype.ext ?_
    rw [hγ, exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_of_eq_zero hker,
      TauCeti.ExteriorAlgebra.ιMulti_of_eq_zero (by rw [h₂, h₃])]
  -- On kernels, `ker (g ∘ f) = ker f` carries `β` to the exterior product of the basis of `ker f`.
  have hK : ∀ e : ker (g ∘ₗ f) ≃ₗ[K] ker f, (∀ z, (e z : M) = z) →
      LinearEquiv.detLineCongr e β = exteriorPower.ιMulti K _ (Module.finBasis K (ker f)) := by
    intro e he
    have hu : ⇑e.toLinearMap ∘ (Submodule.inclusion (ker_le_ker_comp f g) ∘
        Module.finBasis K (ker f)) = Module.finBasis K (ker f) :=
      funext fun i ↦ Subtype.ext (by simp [he])
    refine Subtype.ext ?_
    rw [LinearEquiv.coe_detLineCongr, hβ, ExteriorAlgebra.map_apply_ιMulti,
      TauCeti.ExteriorAlgebra.ιMulti_comp_append, TauCeti.ExteriorAlgebra.ιMulti_of_eq_zero h₂,
      mul_one, hu, exteriorPower.ιMulti_apply_coe]
  -- On cokernels, `g⁻¹` carries `ε` to `δ`, at which `ψ` is normalized, so that the transported
  -- functional is `φ ε • ψ`.
  have hC : ∀ e : (P ⧸ range (g ∘ₗ f)) ≃ₗ[K] (N ⧸ range f),
      (∀ n : N, e (Submodule.Quotient.mk (g n)) = Submodule.Quotient.mk n) →
        φ ∘ₗ (LinearEquiv.detLineCongr e).symm.toLinearMap = φ ε • ψ := by
    intro e he
    have hx : ⇑e.symm.toLinearMap ∘ x = f.cokerToCokerComp g ∘ x := by
      funext i
      obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective _ (x i)
      simp [← hn, LinearEquiv.symm_apply_eq, he]
    have hδ' : (LinearEquiv.detLineCongr e).symm δ = ε := by
      refine Subtype.ext ?_
      rw [LinearEquiv.detLineCongr_symm, LinearEquiv.coe_detLineCongr, hδ,
        ExteriorAlgebra.map_apply_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_append,
        TauCeti.ExteriorAlgebra.ιMulti_of_eq_zero h₃, one_mul, hx, hε,
        TauCeti.ExteriorAlgebra.ιMulti_append_of_eq_zero_right hcoker]
    rw [← Module.Invertible.dual_apply_smul_eq_self hψ (φ ∘ₗ _), LinearMap.comp_apply,
      LinearEquiv.coe_coe, hδ']
  rw [detLineCompEquiv_tmul f g (Module.finBasis K (ker f)) v w x y hβ hγ hδ hε φ hψ hχ,
    detLineCongr_tmul, hK, hC, hunit, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  · exact fun _ ↦ by simp
  · exact fun _ ↦ rfl

/-- **The composition law against a bijective second factor.** If `g` is bijective, its
determinant line is trivialized by `LinearMap.detLineEquivOfBijective`, and the composition law
`det (g ∘ f) ≃ det f ⊗ det g` (`LinearMap.detLineCompEquiv`) sends `x` to the transport of `x`
along the commuting square `f ∘ id = g⁻¹ ∘ (g ∘ f)` (`LinearMap.detLineCongr`) tensored with the
unit of `det g`. So postcomposing with an isomorphism identifies determinant lines exactly as the
transport does, without a sign. -/
theorem detLineCompEquiv_apply_of_bijective_right (hg : Function.Bijective g)
    (x : (g ∘ₗ f).detLine) :
    f.detLineCompEquiv g x =
      (g ∘ₗ f).detLineCongr (LinearEquiv.refl K M) (LinearEquiv.ofBijective g hg).symm
          (by ext; simp) x ⊗ₜ (g.detLineEquivOfBijective hg).symm 1 := by
  have : FiniteDimensional K (P ⧸ range (g ∘ₗ f)) := Module.Finite.quotient_range_comp f g
  obtain ⟨v, w, x₀, y, β, γ, δ, ε, ψ, χ, hβ, hγ, hδ, hε, hψ, hχ, hspan⟩ :=
    TauCeti.exists_spanning_ιMulti_append_sixTerm
      (Submodule.inclusion_injective (ker_le_ker_comp f g)) (f.exact_inclusion_kerCompToKer g)
      (f.exact_kerCompToKer_kerToCoker g) (f.exact_kerToCoker_cokerToCokerComp g)
      (f.exact_cokerToCokerComp_factor g) (Submodule.factor_surjective _)
  -- Both sides are linear in `x`, and `det (ker (g ∘ f))` is spanned by `β`.
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', TensorProduct.add_tmul]
  | tmul z φ =>
    obtain ⟨r, rfl⟩ := hspan z
    rw [← TensorProduct.smul_tmul', map_smul, map_smul, ← TensorProduct.smul_tmul',
      detLineCompEquiv_tmul_of_bijective_right f g hg v w x₀ y hβ hγ hδ hε φ hψ hχ]

end Bijective

end LinearMap
