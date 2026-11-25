/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Exact
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Basic
public import TauCeti.LinearAlgebra.Determinant.Exact
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.LinearIndependent.Fin
import TauCeti.LinearAlgebra.TensorProduct.Dual
import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# The determinant line of a two-periodic complex

Let `C` be a two-periodic complex of finite-dimensional vector spaces over a field `K`, a complex
for the shape `ComplexShape.up (ZMod 2)` with differentials `d₀ : C₀ → C₁` and `d₁ : C₁ → C₀`.
Write `Zᵢ`, `Bᵢ` and `Hᵢ` for its cycles, boundaries and homology, and `C₁ / B₁` for the opcycles
in odd degree. The determinant lines `det V = ⋀^top V` (`TauCeti.detLine`) of its terms and of its
homology are related by a canonical isomorphism, with no choice of bases,

`det C₀ ⊗ (det C₁)^* ≃ det H₀ ⊗ (det H₁)^*`

(`HomologicalComplex.parityDetLineEquiv`), the *determinant readout* of `C`, in the even-then-odd
order. It comes from the two exact sequences

`0 → Z₀ → C₀ → C₁ → C₁ / B₁ → 0` and `0 → H₁ → C₁ / B₁ → Z₀ → H₀ → 0`,

the second being Mathlib's `HomologicalComplex.HomologySequence.composableArrows₃`. By
`TauCeti.detLineFourTermEquiv` the first identifies `det C₀ ⊗ (det C₁)^*` with
`det Z₀ ⊗ (det (C₁ / B₁))^*`, and the second identifies `det (C₁ / B₁) ⊗ (det Z₀)^*` with
`det H₁ ⊗ (det H₀)^*`. The readout is the first isomorphism followed by the inverse transpose of
the second, through the canonical isomorphisms `L ⊗ M^* ≃ (M ⊗ L^*)^*`
(`TensorProduct.dualFlipEquiv`).

The readout is computed by Milnor's recipe for torsion. Choose bases `b₀` of `B₀` and `b₁` of
`B₁`, lifts `s₁ ∈ C₁` of `b₀` through `d₁` and `s₀ ∈ C₀` of `b₁` through `d₀`, and cycles `y₀`,
`y₁` representing bases `h₀`, `h₁` of `H₀`, `H₁`. Then the readout sends
`(b₀ ∧ y₀ ∧ s₀) ⊗ φ` to `φ (b₁ ∧ y₁ ∧ s₁) • (h₀ ⊗ ξ)`, where `ξ` is the functional on `det H₁`
with `ξ h₁ = 1` (`HomologicalComplex.parityDetLineEquiv_tmul`). In particular, for ordered bases
`c₀`, `c₁` of `C₀`, `C₁`, the readout of `c₀ ⊗ c₁^*` is the ratio
`[b₁ y₁ s₁ / c₁] · [b₀ y₀ s₀ / c₀]⁻¹` of the odd bracket by the even bracket times `h₀ ⊗ h₁^*`.

For an acyclic complex the homology vanishes, its determinant lines are `⋀⁰ = K`, and the readout
of `c₀ ⊗ c₁^*` is the torsion `HomologicalComplex.parityTorsion` of the based complex
(`HomologicalComplex.parityDetLineEquiv_tmul_eq_parityTorsion_smul`), normalized so that
multiplication by `a` from the odd to the even degree has torsion `a⁻¹`. Unlike the torsion, which
is `0` on a complex that is not acyclic, the readout is an isomorphism for every complex; it is the
determinant-line refinement of the torsion of two-periodic complexes such as Floer–Novikov
complexes.

## Main definitions

* `HomologicalComplex.parityDetLineEquiv`: the determinant readout
  `det C₀ ⊗ (det C₁)^* ≃ det H₀ ⊗ (det H₁)^*`.

## Main results

* `HomologicalComplex.parityDetLineEquiv_tmul`: its value on exterior products of bases made of
  boundaries, homology representatives and lifts.
* `HomologicalComplex.parityDetLineEquiv_tmul_eq_parityTorsion_smul`: on an acyclic complex, the
  readout of the chain bases is the torsion.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* F. Knudsen, D. Mumford, *The projectivity of the moduli space of stable curves I: Preliminaries
  on "det" and "Div"*, Math. Scand. 39 (1976), 19–55 (determinant lines of complexes).
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Chapter I.
* M. Hutchings, Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and Seiberg–Witten
  invariants of 3-manifolds*, Topology 38 (1999), §2 (torsion of two-periodic complexes).
-/

public section

noncomputable section

open CategoryTheory Module TensorProduct TauCeti
open CochainComplex (prev_zmod_two_zero next_zmod_two_zero prev_zmod_two_one next_zmod_two_one)

namespace HomologicalComplex

variable {K : Type*} [Field K]

/-- Transporting `x ⊗ ξQ` through the flips along an isomorphism `B : Q ⊗ Z^* ≃ H₁ ⊗ H₀^*` of
tensor products of lines, from its values on `ωQ ⊗ φ'` with `ξQ ωQ = 1`. -/
private theorem dualFlipEquiv_symm_dualMap_dualFlipEquiv_tmul {Z Q H₀ H₁ : Type*}
    [AddCommGroup Z] [Module K Z] [AddCommGroup Q] [Module K Q] [AddCommGroup H₀] [Module K H₀]
    [AddCommGroup H₁] [Module K H₁] [FiniteDimensional K Z] [FiniteDimensional K Q]
    [FiniteDimensional K H₀] [FiniteDimensional K H₁] (hQ : finrank K Q = 1)
    (B : Q ⊗[K] Dual K Z ≃ₗ[K] H₁ ⊗[K] Dual K H₀) {x : Z} {ωQ : Q} {ξQ : Dual K Q}
    {η₀ : H₀} {η₁ : H₁} {ξ₀ : Dual K H₀} {ξ : Dual K H₁} (hξQ : ξQ ωQ = 1)
    (hB : ∀ φ', B (ωQ ⊗ₜ φ') = φ' x • (η₁ ⊗ₜ ξ₀)) (hξ₀ : ξ₀ η₀ = 1) (hξ : ξ η₁ = 1) :
    (dualFlipEquiv K H₀ H₁).symm (B.symm.dualMap (dualFlipEquiv K Z Q (x ⊗ₜ ξQ))) =
      η₀ ⊗ₜ ξ := by
  have : Module.Invertible K Q := .of_finrank_eq_one hQ
  refine (LinearEquiv.symm_apply_eq _).2 (LinearMap.ext fun t ↦ ?_)
  obtain ⟨w, rfl⟩ := B.surjective t
  rw [LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply]
  induction w using TensorProduct.inductionOn with
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul q φ' =>
    rw [← Module.Invertible.apply_smul_eq_self hξQ q]
    simp only [← smul_tmul', map_smul, hB, dualFlipEquiv_tmul_tmul, hξQ, hξ, hξ₀, smul_eq_mul,
      mul_one, one_mul]

variable (C : HomologicalComplex (ModuleCat K) (ComplexShape.up (ZMod 2)))
  [FiniteDimensional K (C.X 0)] [FiniteDimensional K (C.X 1)]

/-- The isomorphism `det C₀ ⊗ (det C₁)^* ≃ det Z₀ ⊗ (det (C₁ / B₁))^*` of the exact sequence
`0 → Z₀ → C₀ → C₁ → C₁ / B₁ → 0`. -/
private def evenFourTermEquiv :
    detLine K (C.X 0) ⊗[K] Dual K (detLine K (C.X 1)) ≃ₗ[K]
      detLine K (C.cycles 0) ⊗[K] Dual K (detLine K (C.opcycles 1)) :=
  detLineFourTermEquiv (C.moduleCat_iCycles_injective 0)
    (C.moduleCat_exact_iCycles_d next_zmod_two_zero)
    (C.moduleCat_exact_d_pOpcycles prev_zmod_two_one)
    (C.moduleCat_pOpcycles_surjective 1)

/-- The isomorphism `det (C₁ / B₁) ⊗ (det Z₀)^* ≃ det H₁ ⊗ (det H₀)^*` of the exact sequence
`0 → H₁ → C₁ / B₁ → Z₀ → H₀ → 0`. -/
private def oddFourTermEquiv :
    detLine K (C.opcycles 1) ⊗[K] Dual K (detLine K (C.cycles 0)) ≃ₗ[K]
      detLine K (C.homology 1) ⊗[K] Dual K (detLine K (C.homology 0)) :=
  detLineFourTermEquiv (C.moduleCat_homologyι_injective 1)
    (C.moduleCat_exact_homologyι_opcyclesToCycles (by decide))
    (C.moduleCat_exact_opcyclesToCycles_homologyπ (by decide))
    (C.moduleCat_homologyπ_surjective 0)

/-- The **determinant readout** of a two-periodic complex `C` of finite-dimensional vector spaces:
the canonical isomorphism `det C₀ ⊗ (det C₁)^* ≃ det H₀ ⊗ (det H₁)^*`. It is the isomorphism of
the exact sequence `0 → Z₀ → C₀ → C₁ → C₁ / B₁ → 0`, followed by the inverse transpose of that of
`0 → H₁ → C₁ / B₁ → Z₀ → H₀ → 0`. Its value on exterior products is `parityDetLineEquiv_tmul`; on
an acyclic complex it reads off the torsion (`parityDetLineEquiv_tmul_eq_parityTorsion_smul`). -/
def parityDetLineEquiv :
    detLine K (C.X 0) ⊗[K] Dual K (detLine K (C.X 1)) ≃ₗ[K]
      detLine K (C.homology 0) ⊗[K] Dual K (detLine K (C.homology 1)) :=
  evenFourTermEquiv C ≪≫ₗ dualFlipEquiv K _ _ ≪≫ₗ (oddFourTermEquiv C).symm.dualMap ≪≫ₗ
    (dualFlipEquiv K _ _).symm

/-- The determinant readout as the composite of its four steps. -/
private theorem parityDetLineEquiv_apply
    (t : detLine K (C.X 0) ⊗[K] Dual K (detLine K (C.X 1))) :
    C.parityDetLineEquiv t = (dualFlipEquiv K _ _).symm ((oddFourTermEquiv C).symm.dualMap
      (dualFlipEquiv K _ _ (evenFourTermEquiv C t))) :=
  rfl

variable {C}

/-- The value of the determinant readout, from the values of the two four-term isomorphisms on the
exterior products of bases. -/
private theorem parityDetLineEquiv_tmul_of {β : detLine K (C.X 0)} {φ : Dual K (detLine K (C.X 1))}
    {a : K} {x : detLine K (C.cycles 0)} {ωQ : detLine K (C.opcycles 1)}
    {ξQ : Dual K (detLine K (C.opcycles 1))} {η₀ : detLine K (C.homology 0)}
    {η₁ : detLine K (C.homology 1)} {ξ₀ : Dual K (detLine K (C.homology 0))}
    {ξ : Dual K (detLine K (C.homology 1))}
    (hA : evenFourTermEquiv C (β ⊗ₜ φ) = a • (x ⊗ₜ ξQ)) (hξQ : ξQ ωQ = 1)
    (hB : ∀ φ', oddFourTermEquiv C (ωQ ⊗ₜ φ') = φ' x • (η₁ ⊗ₜ ξ₀)) (hξ₀ : ξ₀ η₀ = 1)
    (hξ : ξ η₁ = 1) :
    C.parityDetLineEquiv (β ⊗ₜ φ) = a • (η₀ ⊗ₜ ξ) := by
  simp only [parityDetLineEquiv_apply, hA, map_smul]
  rw [dualFlipEquiv_symm_dualMap_dualFlipEquiv_tmul (finrank_detLine K _) _ hξQ hB hξ₀ hξ]

/-! ### Dimensions -/

omit [FiniteDimensional K (C.X 1)] in
/-- `dim Z₀ = dim B₀ + dim H₀`. -/
private theorem finrank_cycles_zero :
    finrank K (C.cycles 0) = finrank K (LinearMap.range (C.d 1 0).hom) +
      finrank K (C.homology 0) := by
  have h₁ :=
    C.finrank_X_eq_finrank_range_add_finrank_homology_add prev_zmod_two_zero next_zmod_two_zero
  have h₂ := (C.moduleCat_exact_iCycles_d next_zmod_two_zero).rangeRestrict.finrank_eq_add
    (C.moduleCat_iCycles_injective 0) (C.d 0 1).hom.surjective_rangeRestrict
  omega

omit [FiniteDimensional K (C.X 0)] in
/-- `dim (C₁ / B₁) = dim H₁ + dim B₀`. -/
private theorem finrank_opcycles_one :
    finrank K (C.opcycles 1) = finrank K (C.homology 1) +
      finrank K (LinearMap.range (C.d 1 0).hom) := by
  have h₁ :=
    C.finrank_X_eq_finrank_range_add_finrank_homology_add prev_zmod_two_one next_zmod_two_one
  have h₂ := (C.moduleCat_exact_d_pOpcycles prev_zmod_two_one).range_subtype.finrank_eq_add
    (Submodule.injective_subtype _) (C.moduleCat_pOpcycles_surjective 1)
  omega

omit [FiniteDimensional K (C.X 0)] in
/-- The image of `C₁ / B₁` in `Z₀` has the dimension of `B₀`. -/
private theorem finrank_range_opcyclesToCycles :
    finrank K (LinearMap.range (C.opcyclesToCycles 1 0).hom) =
      finrank K (LinearMap.range (C.d 1 0).hom) := by
  have h₁ := finrank_opcycles_one (C := C)
  have h₂ := (C.moduleCat_exact_homologyι_opcyclesToCycles (by decide)).rangeRestrict.finrank_eq_add
    (C.moduleCat_homologyι_injective 1) (C.opcyclesToCycles 1 0).hom.surjective_rangeRestrict
  omega

/-! ### The values of the two four-term isomorphisms -/

variable {p q m₀ m₁ : ℕ}
  {b₀ : Basis (Fin p) K (LinearMap.range (C.d 1 0).hom)}
  {b₁ : Basis (Fin q) K (LinearMap.range (C.d 0 1).hom)}
  {s₀ : Fin q → C.X 0} {s₁ : Fin p → C.X 1}
  {h₀ : Basis (Fin m₀) K (C.homology 0)} {y₀ : Fin m₀ → C.cycles 0}
  {h₁ : Basis (Fin m₁) K (C.homology 1)} {y₁ : Fin m₁ → C.cycles 1}

omit [FiniteDimensional K (C.X 0)] [FiniteDimensional K (C.X 1)] in
/-- The boundaries of the lifts `s₁` are the cycles `b₀`. -/
private theorem iCycles_toCycles_apply (hs₁ : ∀ l, (C.d 1 0).hom (s₁ l) = b₀ l) (l : Fin p) :
    C.iCycles 0 (C.toCycles 1 0 (s₁ l)) = b₀ l :=
  (C.moduleCat_iCycles_toCycles_apply 0 1 (s₁ l)).trans (hs₁ l)

omit [FiniteDimensional K (C.X 0)] [FiniteDimensional K (C.X 1)] in
/-- The images in `C₁ / B₁` of odd cycles representing homology classes are the images of those
classes. -/
private theorem pOpcycles_comp_iCycles (hy₁ : ∀ k, C.homologyπ 1 (y₁ k) = h₁ k) :
    ((C.pOpcycles 1).hom ∘ fun k ↦ C.iCycles 1 (y₁ k)) = (C.homologyι 1).hom ∘ h₁ :=
  funext fun k ↦ by
    rw [Function.comp_apply, Function.comp_apply, ← hy₁ k]
    exact (C.moduleCat_homologyι_homologyπ_apply 1 (y₁ k)).symm

omit [FiniteDimensional K (C.X 0)] [FiniteDimensional K (C.X 1)] in
/-- The images in `C₁ / B₁` of the odd cycles `y₁` and of the lifts `s₁` are linearly
independent. -/
private theorem linearIndependent_pOpcycles_comp_append (hs₁ : ∀ l, (C.d 1 0).hom (s₁ l) = b₀ l)
    (hy₁ : ∀ k, C.homologyπ 1 (y₁ k) = h₁ k) :
    LinearIndependent K ((C.pOpcycles 1).hom ∘ Fin.append (fun k ↦ C.iCycles 1 (y₁ k)) s₁) := by
  have hgs : LinearIndependent K ((C.opcyclesToCycles 1 0).hom ∘ (C.pOpcycles 1).hom ∘ s₁) :=
    LinearIndependent.of_comp (C.iCycles 0).hom (by
      convert b₀.linearIndependent.map' _ (Submodule.ker_subtype _) using 1
      ext l
      simp [iCycles_toCycles_apply hs₁])
  have hcomp : (C.pOpcycles 1).hom ∘ Fin.append (fun k ↦ C.iCycles 1 (y₁ k)) s₁ =
      Fin.append ((C.homologyι 1).hom ∘ h₁) ((C.pOpcycles 1).hom ∘ s₁) := by
    ext i
    induction i using Fin.addCases <;> simp [← hy₁]
  rw [hcomp]
  refine TauCeti.linearIndependent_fin_append.2
    ⟨h₁.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 (C.moduleCat_homologyι_injective 1)),
      hgs.of_comp _, ?_⟩
  -- The homology lies in the kernel of the map to the cycles, which is injective on the span of
  -- the images of the lifts `s₁`.
  refine ((Submodule.range_ker_disjoint hgs).mono_right ?_).symm
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact (C.moduleCat_exact_homologyι_opcyclesToCycles (by decide) _).2 ⟨h₁ k, rfl⟩

/-- The value of the even four-term isomorphism on the exterior products of the bracket
families. -/
private theorem evenFourTermEquiv_tmul (hs₀ : ∀ l, (C.d 0 1).hom (s₀ l) = b₁ l)
    (hs₁ : ∀ l, (C.d 1 0).hom (s₁ l) = b₀ l) (hZ : finrank K (C.cycles 0) = p + m₀)
    (hq : finrank K (LinearMap.range (C.d 0 1).hom) = q) (hQ : finrank K (C.opcycles 1) = m₁ + p)
    {β : detLine K (C.X 0)}
    (hβ : (β : ExteriorAlgebra K (C.X 0)) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Fin.append (fun l ↦ (b₀ l : C.X 0)) fun k ↦ C.iCycles 0 (y₀ k)) s₀))
    {γ : detLine K (C.X 1)}
    (hγ : (γ : ExteriorAlgebra K (C.X 1)) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Fin.append (fun l ↦ (b₁ l : C.X 1)) fun k ↦ C.iCycles 1 (y₁ k)) s₁))
    (φ : Dual K (detLine K (C.X 1))) {ξQ : Dual K (detLine K (C.opcycles 1))}
    (hξQ : ξQ (exteriorPower.ιMulti K _ ((C.pOpcycles 1).hom ∘
      Fin.append (fun k ↦ C.iCycles 1 (y₁ k)) s₁ ∘ Fin.cast hQ)) = 1) :
    evenFourTermEquiv C (β ⊗ₜ φ) = φ γ • (exteriorPower.ιMulti K _
      (Fin.append (fun l ↦ C.toCycles 1 0 (s₁ l)) y₀ ∘ Fin.cast hZ) ⊗ₜ ξQ) := by
  have e₀ : (C.iCycles 0).hom ∘ Fin.append (fun l ↦ C.toCycles 1 0 (s₁ l)) y₀ =
      Fin.append (fun l ↦ (b₀ l : C.X 0)) fun k ↦ C.iCycles 0 (y₀ k) := by
    funext i
    induction i using Fin.addCases <;> simp [iCycles_toCycles_apply hs₁]
  have e₁ : (C.d 0 1).hom ∘ s₀ = fun l ↦ (b₁ l : C.X 1) := funext hs₀
  refine detLineFourTermEquiv_tmul_eq_smul_tmul _ _ _ _ _ (s₀ ∘ Fin.cast hq) _ ?_ ?_ φ hξQ
  · calc (β : ExteriorAlgebra K (C.X 0))
        = ExteriorAlgebra.ιMulti K (p + m₀) ((C.iCycles 0).hom ∘
            Fin.append (fun l ↦ C.toCycles 1 0 (s₁ l)) y₀) * ExteriorAlgebra.ιMulti K q s₀ := by
          rw [hβ, e₀, ExteriorAlgebra.ιMulti_mul_ιMulti]
      _ = _ := (TauCeti.ExteriorAlgebra.ιMulti_append_comp_cast _ _ hZ hq).symm
  · calc (γ : ExteriorAlgebra K (C.X 1))
        = ExteriorAlgebra.ιMulti K q (fun l ↦ (b₁ l : C.X 1)) *
            ExteriorAlgebra.ιMulti K (m₁ + p) (Fin.append (fun k ↦ C.iCycles 1 (y₁ k)) s₁) := by
          rw [hγ]
          simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, mul_assoc]
      _ = ExteriorAlgebra.ιMulti K q ((C.d 0 1).hom ∘ s₀) *
            ExteriorAlgebra.ιMulti K (m₁ + p) (Fin.append (fun k ↦ C.iCycles 1 (y₁ k)) s₁) := by
          rw [e₁]
      _ = _ := (TauCeti.ExteriorAlgebra.ιMulti_append_comp_cast _ _ hq hQ).symm

/-- The value of the odd four-term isomorphism on the exterior products of the bracket
families. -/
private theorem oddFourTermEquiv_tmul (hy₀ : ∀ k, C.homologyπ 0 (y₀ k) = h₀ k)
    (hy₁ : ∀ k, C.homologyπ 1 (y₁ k) = h₁ k) (hZ : finrank K (C.cycles 0) = p + m₀)
    (hQ : finrank K (C.opcycles 1) = m₁ + p)
    (hR : finrank K (LinearMap.range (C.opcyclesToCycles 1 0).hom) = p)
    (hm₀ : finrank K (C.homology 0) = m₀) (hm₁ : finrank K (C.homology 1) = m₁)
    (φ' : Dual K (detLine K (C.cycles 0))) {ξ₀ : Dual K (detLine K (C.homology 0))}
    (hξ₀ : ξ₀ (exteriorPower.ιMulti K _ (h₀ ∘ Fin.cast hm₀)) = 1) :
    oddFourTermEquiv C (exteriorPower.ιMulti K _ ((C.pOpcycles 1).hom ∘
        Fin.append (fun k ↦ C.iCycles 1 (y₁ k)) s₁ ∘ Fin.cast hQ) ⊗ₜ φ') =
      φ' (exteriorPower.ιMulti K _ (Fin.append (fun l ↦ C.toCycles 1 0 (s₁ l)) y₀ ∘
        Fin.cast hZ)) • (exteriorPower.ιMulti K _ (h₁ ∘ Fin.cast hm₁) ⊗ₜ ξ₀) := by
  have e : ((C.opcyclesToCycles 1 0).hom ∘ (C.pOpcycles 1).hom ∘ s₁) =
      fun l ↦ C.toCycles 1 0 (s₁ l) :=
    funext fun l ↦ C.moduleCat_opcyclesToCycles_pOpcycles_apply 1 0 (s₁ l)
  refine detLineFourTermEquiv_tmul_eq_smul_tmul _ _ _ _ (h₁ ∘ Fin.cast hm₁)
    ((C.pOpcycles 1).hom ∘ s₁ ∘ Fin.cast hR) (y₀ ∘ Fin.cast hm₀) ?_ ?_ φ' ?_
  · rw [exteriorPower.ιMulti_apply_coe]
    calc _ = ExteriorAlgebra.ιMulti K (m₁ + p)
            ((C.pOpcycles 1).hom ∘ Fin.append (fun k ↦ C.iCycles 1 (y₁ k)) s₁) :=
          TauCeti.ExteriorAlgebra.ιMulti_comp_cast hQ _
      _ = ExteriorAlgebra.ιMulti K m₁ ((C.homologyι 1).hom ∘ h₁) *
            ExteriorAlgebra.ιMulti K p ((C.pOpcycles 1).hom ∘ s₁) := by
          rw [TauCeti.ExteriorAlgebra.ιMulti_comp_append, pOpcycles_comp_iCycles hy₁]
      _ = _ := (TauCeti.ExteriorAlgebra.ιMulti_append_comp_cast _ _ hm₁ hR).symm
  · rw [exteriorPower.ιMulti_apply_coe]
    calc _ = ExteriorAlgebra.ιMulti K p (fun l ↦ C.toCycles 1 0 (s₁ l)) *
            ExteriorAlgebra.ιMulti K m₀ y₀ := by
          rw [TauCeti.ExteriorAlgebra.ιMulti_comp_cast, ExteriorAlgebra.ιMulti_mul_ιMulti]
      _ = ExteriorAlgebra.ιMulti K p
            ((C.opcyclesToCycles 1 0).hom ∘ (C.pOpcycles 1).hom ∘ s₁) *
            ExteriorAlgebra.ιMulti K m₀ y₀ := by
          rw [e]
      _ = _ := (TauCeti.ExteriorAlgebra.ιMulti_append_comp_cast _ _ hR hm₀).symm
  · convert hξ₀ using 3
    funext k
    exact hy₀ (Fin.cast hm₀ k)

/-- **The value of the determinant readout.** Let `b₀`, `b₁` be bases of the boundaries
`B₀ = im d₁` and `B₁ = im d₀`, `s₁` lifts of `b₀` through `d₁` and `s₀` lifts of `b₁` through
`d₀`, and `y₀`, `y₁` cycles representing bases `h₀`, `h₁` of the homology. Let `β ∈ det C₀` and
`γ ∈ det C₁` be the exterior products of `(b₀, y₀, s₀)` and `(b₁, y₁, s₁)`, `η₀`, `η₁` those of
`h₀`, `h₁`, and `ξ` a functional on `det H₁` with `ξ η₁ = 1`. Then the readout sends `β ⊗ φ` to
`φ γ • (η₀ ⊗ ξ)`. -/
theorem parityDetLineEquiv_tmul (hs₀ : ∀ l, (C.d 0 1).hom (s₀ l) = b₁ l)
    (hs₁ : ∀ l, (C.d 1 0).hom (s₁ l) = b₀ l) (hy₀ : ∀ k, C.homologyπ 0 (y₀ k) = h₀ k)
    (hy₁ : ∀ k, C.homologyπ 1 (y₁ k) = h₁ k) {β : detLine K (C.X 0)}
    (hβ : (β : ExteriorAlgebra K (C.X 0)) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Fin.append (fun l ↦ (b₀ l : C.X 0)) fun k ↦ C.iCycles 0 (y₀ k)) s₀))
    {γ : detLine K (C.X 1)}
    (hγ : (γ : ExteriorAlgebra K (C.X 1)) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Fin.append (fun l ↦ (b₁ l : C.X 1)) fun k ↦ C.iCycles 1 (y₁ k)) s₁))
    (φ : Dual K (detLine K (C.X 1))) {η₀ : detLine K (C.homology 0)}
    (hη₀ : (η₀ : ExteriorAlgebra K (C.homology 0)) = ExteriorAlgebra.ιMulti K m₀ h₀)
    {η₁ : detLine K (C.homology 1)}
    (hη₁ : (η₁ : ExteriorAlgebra K (C.homology 1)) = ExteriorAlgebra.ιMulti K m₁ h₁)
    {ξ : Dual K (detLine K (C.homology 1))} (hξ : ξ η₁ = 1) :
    C.parityDetLineEquiv (β ⊗ₜ φ) = φ γ • (η₀ ⊗ₜ ξ) := by
  have hp : finrank K (LinearMap.range (C.d 1 0).hom) = p := by
    rw [finrank_eq_card_basis b₀, Fintype.card_fin]
  have hq : finrank K (LinearMap.range (C.d 0 1).hom) = q := by
    rw [finrank_eq_card_basis b₁, Fintype.card_fin]
  have hm₀ : finrank K (C.homology 0) = m₀ := by rw [finrank_eq_card_basis h₀, Fintype.card_fin]
  have hm₁ : finrank K (C.homology 1) = m₁ := by rw [finrank_eq_card_basis h₁, Fintype.card_fin]
  have hZ : finrank K (C.cycles 0) = p + m₀ := by rw [finrank_cycles_zero, hp, hm₀]
  have hQ : finrank K (C.opcycles 1) = m₁ + p := by rw [finrank_opcycles_one, hm₁, hp]
  have hR : finrank K (LinearMap.range (C.opcyclesToCycles 1 0).hom) = p := by
    rw [finrank_range_opcyclesToCycles, hp]
  -- Functionals normalized on the exterior products of the bases of `C₁ / B₁` and of `H₀`.
  obtain ⟨ξQ, hξQ⟩ := Module.Projective.exists_dual_eq_one K
    ((exteriorPower.ιMulti_ne_zero_iff ((C.pOpcycles 1).hom ∘
      Fin.append (fun k ↦ C.iCycles 1 (y₁ k)) s₁ ∘ Fin.cast hQ)).2
      ((linearIndependent_pOpcycles_comp_append hs₁ hy₁).comp _ (Fin.cast_injective hQ)))
  obtain ⟨ξ₀, hξ₀⟩ := Module.Projective.exists_dual_eq_one K
    ((exteriorPower.ιMulti_ne_zero_iff (h₀ ∘ Fin.cast hm₀)).2
      (h₀.linearIndependent.comp _ (Fin.cast_injective hm₀)))
  have e₀ : exteriorPower.ιMulti K _ (h₀ ∘ Fin.cast hm₀) = η₀ := Subtype.ext (by
    rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast, hη₀])
  have e₁ : exteriorPower.ιMulti K _ (h₁ ∘ Fin.cast hm₁) = η₁ := Subtype.ext (by
    rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast, hη₁])
  exact parityDetLineEquiv_tmul_of (evenFourTermEquiv_tmul hs₀ hs₁ hZ hq hQ hβ hγ φ hξQ) hξQ
    (fun φ' ↦ (oddFourTermEquiv_tmul hy₀ hy₁ hZ hQ hR hm₀ hm₁ φ' hξ₀).trans (by rw [e₁]))
    (e₀ ▸ hξ₀) hξ

/-! ### Acyclic complexes -/

omit [FiniteDimensional K (C.X 0)] [FiniteDimensional K (C.X 1)] in
/-- The exterior product of a boundary basis followed by lifts is the bracket times the exterior
product of the chain basis. -/
private theorem ιMulti_append_eq_torsionBracket_smul {n : ZMod 2 → ℕ}
    (c : ∀ i, Basis (Fin (n i)) K (C.X i)) {i j k : ZMod 2}
    (hi : (ComplexShape.up (ZMod 2)).prev j = i) (hk : (ComplexShape.up (ZMod 2)).next j = k)
    (h : C.ExactAt j) {p q : ℕ} (b : Basis (Fin p) K (LinearMap.range (C.d i j).hom))
    (b' : Basis (Fin q) K (LinearMap.range (C.d j k).hom)) (s : Fin q → C.X j)
    (hs : ∀ l, (C.d j k).hom (s l) = b' l) {ω : detLine K (C.X j)}
    (hω : (ω : ExteriorAlgebra K (C.X j)) = ExteriorAlgebra.ιMulti K (n j) (c j)) :
    ExteriorAlgebra.ιMulti K (p + q) (Fin.append (fun l ↦ (b l : C.X j)) s) =
      torsionBracket c hi hk h b b' s hs • (ω : ExteriorAlgebra K (C.X j)) := by
  have hn := eq_add_of_exactAt c hi hk h b b'
  rw [torsionBracket_eq_det_append c hi hk h b b' s hs hn, hω,
    ← TauCeti.ExteriorAlgebra.ιMulti_comp_cast hn]
  exact congrArg Subtype.val ((c j).exteriorPower_ιMulti_eq_det_smul _)

omit [FiniteDimensional K (C.X 0)] [FiniteDimensional K (C.X 1)] in
/-- The bracket times the exterior product of the chain basis is the exterior product of the
boundary basis, an empty family of homology representatives and the lifts. -/
private theorem coe_torsionBracket_smul {n : ZMod 2 → ℕ} (c : ∀ i, Basis (Fin (n i)) K (C.X i))
    {i j k : ZMod 2} (hi : (ComplexShape.up (ZMod 2)).prev j = i)
    (hk : (ComplexShape.up (ZMod 2)).next j = k) (h : C.ExactAt j) {p q : ℕ}
    (b : Basis (Fin p) K (LinearMap.range (C.d i j).hom))
    (b' : Basis (Fin q) K (LinearMap.range (C.d j k).hom)) (s : Fin q → C.X j)
    (hs : ∀ l, (C.d j k).hom (s l) = b' l) {ω : detLine K (C.X j)}
    (hω : (ω : ExteriorAlgebra K (C.X j)) = ExteriorAlgebra.ιMulti K (n j) (c j)) :
    ((torsionBracket c hi hk h b b' s hs • ω : detLine K (C.X j)) : ExteriorAlgebra K (C.X j)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (Fin.append (fun l ↦ (b l : C.X j))
        fun k : Fin 0 ↦ C.iCycles j (Fin.elim0 k)) s) := by
  rw [Submodule.coe_smul, ← ιMulti_append_eq_torsionBracket_smul c hi hk h b b' s hs hω]
  simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

/-- On an acyclic complex, the readout of the chain bases times the even bracket is the odd bracket
times the readout of the empty homology bases. -/
private theorem torsionBracket_smul_parityDetLineEquiv_tmul (h : C.Acyclic) {n : ZMod 2 → ℕ}
    (c : ∀ i, Basis (Fin (n i)) K (C.X i)) {p q : ℕ}
    (b₀ : Basis (Fin p) K (LinearMap.range (C.d 1 0).hom))
    (b₁ : Basis (Fin q) K (LinearMap.range (C.d 0 1).hom)) (s₀ : Fin q → C.X 0)
    (hs₀ : ∀ l, (C.d 0 1).hom (s₀ l) = b₁ l) (s₁ : Fin p → C.X 1)
    (hs₁ : ∀ l, (C.d 1 0).hom (s₁ l) = b₀ l) {ω₀ : detLine K (C.X 0)}
    (hω₀ : (ω₀ : ExteriorAlgebra K (C.X 0)) = ExteriorAlgebra.ιMulti K (n 0) (c 0))
    {ω₁ : detLine K (C.X 1)}
    (hω₁ : (ω₁ : ExteriorAlgebra K (C.X 1)) = ExteriorAlgebra.ιMulti K (n 1) (c 1))
    {ξ₁ : Dual K (detLine K (C.X 1))} (hξ₁ : ξ₁ ω₁ = 1) {η₀ : detLine K (C.homology 0)}
    (hη₀ : (η₀ : ExteriorAlgebra K (C.homology 0)) = 1) {η₁ : detLine K (C.homology 1)}
    (hη₁ : (η₁ : ExteriorAlgebra K (C.homology 1)) = 1) {ξ : Dual K (detLine K (C.homology 1))}
    (hξ : ξ η₁ = 1) :
    torsionBracket c prev_zmod_two_zero next_zmod_two_zero (h 0) b₀ b₁ s₀ hs₀ •
        C.parityDetLineEquiv (ω₀ ⊗ₜ ξ₁) =
      torsionBracket c prev_zmod_two_one next_zmod_two_one (h 1) b₁ b₀ s₁ hs₁ • (η₀ ⊗ₜ ξ) := by
  have : Subsingleton (C.homology 0) := ModuleCat.subsingleton_of_isZero (h 0).isZero_homology
  have : Subsingleton (C.homology 1) := ModuleCat.subsingleton_of_isZero (h 1).isZero_homology
  have hβ := coe_torsionBracket_smul c prev_zmod_two_zero next_zmod_two_zero (h 0) b₀ b₁ s₀ hs₀ hω₀
  have hγ := coe_torsionBracket_smul c prev_zmod_two_one next_zmod_two_one (h 1) b₁ b₀ s₁ hs₁ hω₁
  generalize torsionBracket c _ _ (h 0) b₀ b₁ s₀ hs₀ = B₀ at hβ ⊢
  generalize torsionBracket c _ _ (h 1) b₁ b₀ s₁ hs₁ = B₁ at hγ ⊢
  have hξB₁ : ξ₁ (B₁ • ω₁) = B₁ := by rw [map_smul, hξ₁, smul_eq_mul, mul_one]
  rw [← map_smul, smul_tmul' B₀ ω₀ ξ₁]
  exact (parityDetLineEquiv_tmul (C := C) (h₀ := Basis.empty _) (h₁ := Basis.empty _)
    (y₀ := Fin.elim0) (y₁ := Fin.elim0) hs₀ hs₁ (fun k ↦ k.elim0) (fun k ↦ k.elim0) hβ hγ ξ₁
    (by rw [hη₀, ExteriorAlgebra.ιMulti_zero_apply])
    (by rw [hη₁, ExteriorAlgebra.ιMulti_zero_apply]) hξ).trans
    (congrArg (· • (η₀ ⊗ₜ[K] ξ)) hξB₁)

/-- **On an acyclic complex the determinant readout is the torsion.** Let `ω₀`, `ω₁` be the
exterior products of ordered bases `c 0`, `c 1` of `C₀`, `C₁`, and `ξ₁` the functional on `det C₁`
with `ξ₁ ω₁ = 1`. The homology of an acyclic complex vanishes; let `η₀ ∈ det H₀` and
`η₁ ∈ det H₁` be the empty exterior products `1`, and `ξ` the functional on `det H₁` with
`ξ η₁ = 1`. Then the readout sends `ω₀ ⊗ ξ₁` to `τ(C, c) • (η₀ ⊗ ξ)`, where `τ(C, c)` is the
torsion `HomologicalComplex.parityTorsion`. -/
theorem parityDetLineEquiv_tmul_eq_parityTorsion_smul (h : C.Acyclic) {n : ZMod 2 → ℕ}
    (c : ∀ i, Basis (Fin (n i)) K (C.X i)) {ω₀ : detLine K (C.X 0)}
    (hω₀ : (ω₀ : ExteriorAlgebra K (C.X 0)) = ExteriorAlgebra.ιMulti K (n 0) (c 0))
    {ω₁ : detLine K (C.X 1)}
    (hω₁ : (ω₁ : ExteriorAlgebra K (C.X 1)) = ExteriorAlgebra.ιMulti K (n 1) (c 1))
    {ξ₁ : Dual K (detLine K (C.X 1))} (hξ₁ : ξ₁ ω₁ = 1) {η₀ : detLine K (C.homology 0)}
    (hη₀ : (η₀ : ExteriorAlgebra K (C.homology 0)) = 1) {η₁ : detLine K (C.homology 1)}
    (hη₁ : (η₁ : ExteriorAlgebra K (C.homology 1)) = 1) {ξ : Dual K (detLine K (C.homology 1))}
    (hξ : ξ η₁ = 1) :
    C.parityDetLineEquiv (ω₀ ⊗ₜ ξ₁) = C.parityTorsion c • (η₀ ⊗ₜ ξ) := by
  -- Boundary bases and lifts, as opaque variables.
  obtain ⟨p, b₀, s₁, hs₁⟩ : ∃ p, ∃ b₀ : Basis (Fin p) K (LinearMap.range (C.d 1 0).hom),
      ∃ s₁ : Fin p → C.X 1, ∀ l, (C.d 1 0).hom (s₁ l) = b₀ l :=
    ⟨_, _, _, chosenBoundaryLift_spec C c 1 0⟩
  obtain ⟨q, b₁, s₀, hs₀⟩ : ∃ q, ∃ b₁ : Basis (Fin q) K (LinearMap.range (C.d 0 1).hom),
      ∃ s₀ : Fin q → C.X 0, ∀ l, (C.d 0 1).hom (s₀ l) = b₁ l :=
    ⟨_, _, _, chosenBoundaryLift_spec C c 0 1⟩
  have key := torsionBracket_smul_parityDetLineEquiv_tmul h c b₀ b₁ s₀ hs₀ s₁ hs₁ hω₀ hω₁ hξ₁ hη₀
    hη₁ hξ
  have hB₀ := torsionBracket_ne_zero c prev_zmod_two_zero next_zmod_two_zero (h 0) b₀ b₁ s₀ hs₀
  rw [parityTorsion_eq h b₀ b₁ s₀ hs₀ s₁ hs₁, mul_comm, ← smul_smul, eq_inv_smul_iff₀ hB₀]
  exact key

end HomologicalComplex
