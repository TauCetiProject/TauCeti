/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Hom.Cohomology

/-!
# Homological transfer of A-infinity bimodules

Let `M` be an `(A, B)` `A∞` bimodule, and let `(i, p, h)` be a special contraction of `(M, m₁)`
onto a graded module `(N, d_N)`, with `h` of degree `-1` and `i`, `p` of degree zero.  The bimodule
is stored on its cofree bar bicomodule `Tᶜ(sA) ⊗ sM ⊗ Tᶜ(sB)` by a square-zero coderivation `D`,
over the bar differential `b_A` of `A` for the left coaction and over `b_B` for the right one.
Split it as `D = D₀ + δ`, where on `w ⊗ x ⊗ v`

`D₀ (w ⊗ x ⊗ v) = b_A w ⊗ x ⊗ v + τ w ⊗ m₁ x ⊗ v + τ w ⊗ τ x ⊗ b_B v`

(`TauCeti.AInfinityBimodule.unaryBarDifferential`) only involves the unary operation, with `τ`
the Koszul twists of the suspended gradings, and the *higher* part `δ`
(`TauCeti.AInfinityBimodule.higherBarDifferential`) applies the operations `b_{i,j}` with
`i + j ≥ 1` to the middle blocks of a word (see
`TauCeti.Algebra.Homology.AInfinity.Bimodule.BarDifferential`).  Thus `δ` strictly lowers the
total length of the two algebra words, and, unlike `D₀`, it is an odd map of left comodules and a
map of right comodules.

The contraction induces the special contraction `(1 ⊗ i ⊗ 1, 1 ⊗ p ⊗ 1, τ ⊗ h ⊗ 1)` of the bar
bicomodules for the unary parts (`TauCeti.AInfinityBimodule.barContraction`): it is the contraction
of `Tᶜ(sA) ⊗ M` tensored on the left with `(Tᶜ(sA), b_A)`
(`TauCeti.LinearSpecialContraction.lTensor`), then on the right with `(Tᶜ(sB), b_B)`.  The basic
perturbation lemma transports it along `δ`.  As `τ ⊗ h ⊗ 1` preserves both word lengths,
`δ (τ ⊗ h ⊗ 1)` is locally nilpotent, so the perturbation operator
`X = (1 + δ (τ ⊗ h ⊗ 1))⁻¹ δ` exists.  Both `δ` and `τ ⊗ h ⊗ 1` are odd maps of left comodules
and maps of right comodules, so `X` is too, and the perturbed differential
`D' = D₀' + (1 ⊗ p ⊗ 1) X (1 ⊗ i ⊗ 1)` is again a bicomodule coderivation over `b_A` and `b_B`,
squaring to zero.  It is the bar differential of the *transferred* bimodule structure on `N`
(`TauCeti.AInfinityBimodule.transfer`), whose unary operation is `d_N`.  The perturbed inclusion
and projection are maps of bicomodules intertwining the bar differentials, hence morphisms of
`A∞` bimodules `TauCeti.AInfinityBimodule.transferInclusion` and
`TauCeti.AInfinityBimodule.transferProjection` with linear parts `i` and `p`.  Both are
quasi-isomorphisms, and the projection is a left inverse of the inclusion.

The construction follows the transfer of right `A∞` modules,
`TauCeti.AInfinityRightModule.transfer` in
`TauCeti.Algebra.Homology.AInfinity.Module.Right.Transfer`; the bar bicomodule is the bar comodule
of the right module `Tᶜ(sA) ⊗ M` over `B`, and the new ingredient is the left coaction, for which
the Koszul sign of the homotopy makes the perturbation data odd maps of left comodules.

## Main definitions

* `TauCeti.AInfinityBimodule.barContraction`: the contraction of bar bicomodules induced by a
  contraction of the bimodule.
* `TauCeti.AInfinityBimodule.transferBarDifferential`: the perturbed differential `D'`.
* `TauCeti.AInfinityBimodule.transferContraction`: the perturbed contraction of bar bicomodules.
* `TauCeti.AInfinityBimodule.transfer`: the transferred `A∞` bimodule structure.
* `TauCeti.AInfinityBimodule.transferInclusion` and
  `TauCeti.AInfinityBimodule.transferProjection`: the morphisms of `A∞` bimodules extending the
  inclusion and the projection.

## Main results

* `TauCeti.AInfinityBimodule.leftCoact_comp_perturbationSeries` and
  `TauCeti.AInfinityBimodule.coact_comp_perturbationSeries`: the perturbation operator respects
  both coactions.
* `TauCeti.AInfinityBimodule.barDifferential_transfer` and
  `TauCeti.AInfinityBimodule.differential_transfer`: the bar differential of the transferred
  bimodule is the perturbed differential, and its unary operation is `d_N`.
* `TauCeti.AInfinityBimodule.linearPart_transferInclusion` and
  `TauCeti.AInfinityBimodule.linearPart_transferProjection`: the linear parts are `i` and `p`.
* `TauCeti.AInfinityBimodule.transferProjection_comp_transferInclusion`: the projection is a
  left inverse of the inclusion.
* `TauCeti.AInfinityBimodule.isQuasiIso_transferInclusion` and
  `TauCeti.AInfinityBimodule.isQuasiIso_transferProjection`: both are quasi-isomorphisms.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 4 and 5.
* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
-/

public section

open scoped TensorProduct

universe uR uA uB uM uN

namespace TauCeti

open TensorWords

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace AInfinityBimodule

attribute [local instance] Comodule.cofree leftCoactCarrierAddCommGroup

/-! ### The bar contraction and the perturbation -/

section Transfer

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} (MM : AInfinityBimodule AA BB M)
  {GN : InternalGrading R N ℤ} {dN : Module.End R N}
  (c : LinearSpecialContraction MM.differential dN)
  (hh : LinearMap.IsHomogeneous c.homotopy MM.grading.piece MM.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GN.piece MM.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj MM.grading.piece GN.piece 0)

/-- The unary part is the tensor product differential of `Tᶜ(sA) ⊗ M` with `Tᶜ(sB)`. -/
theorem unaryBarDifferential_eq_rTensor_add (G : InternalGrading R M ℤ) (d : Module.End R M) :
    unaryBarDifferential AA BB G d =
      (leftUnaryDifferential AA d).rTensor (TensorWords R B) +
        BB.coaugmentedBarDifferential.lTensor (TensorWords R A ⊗[R] M) ∘ₗ
          (((leftGrading AA G).shift 1).koszulTwist 1).rTensor (TensorWords R B) := by
  rw [unaryBarDifferential_def, AInfinityRightModule.unaryBarDifferential_def]

/-- A homogeneous map `g` gives a map `1 ⊗ g` of the same degree for the left gradings. -/
private theorem isHomogeneous_lTensor_leftGrading {G : InternalGrading R M ℤ}
    {G' : InternalGrading R N ℤ} {g : M →ₗ[R] N} {r : ℤ}
    (hg : LinearMap.IsHomogeneous g G.piece G'.piece r) :
    LinearMap.IsHomogeneous (g.lTensor (TensorWords R A)) ((leftGrading AA G).shift 1).piece
      ((leftGrading AA G').shift 1).piece r := by
  rw [shift_one_leftGrading, shift_one_leftGrading, LinearMap.lTensor_def]
  simpa only [zero_add] using (LinearMap.isHomogeneous_id
    (TensorWords.grading (AA.grading.shift 1)).piece).tensorProduct
      (LinearMap.isHomogeneous_shift_piece_iff.2 hg)

/-- A homogeneous map `g` gives a map `τ ⊗ g` of the same degree for the left gradings. -/
private theorem isHomogeneous_map_koszulTwist_leftGrading {G : InternalGrading R M ℤ}
    {G' : InternalGrading R N ℤ} {g : M →ₗ[R] N} {r : ℤ}
    (hg : LinearMap.IsHomogeneous g G.piece G'.piece r) :
    LinearMap.IsHomogeneous
      (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) g)
      ((leftGrading AA G).shift 1).piece ((leftGrading AA G').shift 1).piece r := by
  let W := TensorWords.grading (AA.grading.shift 1)
  have hτ : LinearMap.IsHomogeneous (W.koszulTwist 1) W.piece W.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      simpa only [add_zero] using W.koszulTwist_mem_piece hx 1
  rw [shift_one_leftGrading, shift_one_leftGrading]
  simpa only [zero_add] using hτ.tensorProduct (LinearMap.isHomogeneous_shift_piece_iff.2 hg)

/-- A homogeneous map `f` of `Tᶜ(sA) ⊗ sM` gives a map `f ⊗ 1` of the same degree for the bar
gradings. -/
private theorem isHomogeneous_rTensor_of_leftGrading {G : InternalGrading R M ℤ}
    {G' : InternalGrading R N ℤ} {f : TensorWords R A ⊗[R] M →ₗ[R] TensorWords R A ⊗[R] N} {r : ℤ}
    (hf : LinearMap.IsHomogeneous f ((leftGrading AA G).shift 1).piece
      ((leftGrading AA G').shift 1).piece r) :
    LinearMap.IsHomogeneous (f.rTensor (TensorWords R B))
      (barGrading AA BB G).piece (barGrading AA BB G').piece r := by
  have h := AInfinityRightModule.isHomogeneous_rTensor (AA := BB)
    (M := TensorWords R A ⊗[R] M) (N := TensorWords R A ⊗[R] N)
    (LinearMap.isHomogeneous_shift_piece_iff.1 hf)
  rwa [rightModule_barGrading_leftGrading, rightModule_barGrading_leftGrading] at h

/-- The contraction `(1 ⊗ i, 1 ⊗ p, τ ⊗ h)` of `(Tᶜ(sA) ⊗ M, b_A ⊗ 1 + τ ⊗ m₁)` onto
`(Tᶜ(sA) ⊗ N, b_A ⊗ 1 + τ ⊗ d_N)` induced by a special contraction of `(M, m₁)`. -/
noncomputable def leftContraction :
    LinearSpecialContraction (M := TensorWords R A ⊗[R] M) (N := TensorWords R A ⊗[R] N)
      (leftUnaryDifferential AA MM.differential) (leftUnaryDifferential AA dN) :=
  c.lTensor (isHomogeneous_coaugmentedBarDifferential_grading AA)

/-- The inclusion of the left contraction is `1 ⊗ i`. -/
@[simp]
theorem leftContraction_incl :
    (MM.leftContraction c).incl = c.incl.lTensor (TensorWords R A) :=
  LinearSpecialContraction.lTensor_incl ..

/-- The projection of the left contraction is `1 ⊗ p`. -/
@[simp]
theorem leftContraction_proj :
    (MM.leftContraction c).proj = c.proj.lTensor (TensorWords R A) :=
  LinearSpecialContraction.lTensor_proj ..

/-- The homotopy of the left contraction is `τ ⊗ h`. -/
@[simp]
theorem leftContraction_homotopy :
    (MM.leftContraction c).homotopy =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) c.homotopy :=
  LinearSpecialContraction.lTensor_homotopy ..

/-- The **bar contraction**: a special contraction of `(M, m₁)` onto `(N, d_N)` induces the
special contraction `(1 ⊗ i ⊗ 1, 1 ⊗ p ⊗ 1, τ ⊗ h ⊗ 1)` of the bar bicomodules
`Tᶜ(sA) ⊗ sM ⊗ Tᶜ(sB)` onto `Tᶜ(sA) ⊗ sN ⊗ Tᶜ(sB)` for the unary parts of the bar
differentials. -/
noncomputable def barContraction :
    LinearSpecialContraction (unaryBarDifferential AA BB MM.grading MM.differential)
      (unaryBarDifferential AA BB GN dN) :=
  let c' := (MM.leftContraction c).rTensor
    (by rw [leftContraction_homotopy]; exact isHomogeneous_map_koszulTwist_leftGrading hh)
    (by rw [leftContraction_incl]; exact isHomogeneous_lTensor_leftGrading hincl)
    (by rw [leftContraction_proj]; exact isHomogeneous_lTensor_leftGrading hproj)
    BB.coaugmentedBarDifferential
  { incl := c'.incl
    proj := c'.proj
    homotopy := c'.homotopy
    dM_comp_incl := by
      rw [unaryBarDifferential_eq_rTensor_add, unaryBarDifferential_eq_rTensor_add]
      exact c'.dM_comp_incl
    proj_comp_dM := by
      rw [unaryBarDifferential_eq_rTensor_add, unaryBarDifferential_eq_rTensor_add]
      exact c'.proj_comp_dM
    proj_comp_incl := c'.proj_comp_incl
    dM_comp_homotopy_add_homotopy_comp_dM := by
      rw [unaryBarDifferential_eq_rTensor_add]
      exact c'.dM_comp_homotopy_add_homotopy_comp_dM
    homotopy_comp_incl := c'.homotopy_comp_incl
    proj_comp_homotopy := c'.proj_comp_homotopy
    homotopy_comp_homotopy := c'.homotopy_comp_homotopy }

/-- The inclusion of the bar contraction is `1 ⊗ i ⊗ 1`. -/
@[simp]
theorem barContraction_incl :
    (MM.barContraction c hh hincl hproj).incl =
      (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B) := by
  simp only [barContraction, LinearSpecialContraction.rTensor_incl, leftContraction_incl]

/-- The projection of the bar contraction is `1 ⊗ p ⊗ 1`. -/
@[simp]
theorem barContraction_proj :
    (MM.barContraction c hh hincl hproj).proj =
      (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) := by
  simp only [barContraction, LinearSpecialContraction.rTensor_proj, leftContraction_proj]

/-- The homotopy of the bar contraction is `τ ⊗ h ⊗ 1`. -/
@[simp]
theorem barContraction_homotopy :
    (MM.barContraction c hh hincl hproj).homotopy =
      (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
        c.homotopy).rTensor (TensorWords R B) := by
  simp only [barContraction, LinearSpecialContraction.rTensor_homotopy, leftContraction_homotopy]

/-- The source differential of the bar contraction squares to zero. -/
theorem unaryBarDifferential_differential_comp_self :
    unaryBarDifferential AA BB MM.grading MM.differential ∘ₗ
      unaryBarDifferential AA BB MM.grading MM.differential = 0 :=
  unaryBarDifferential_comp_self AA BB MM.grading
    (LinearMap.isHomogeneous_shift_piece_iff.2 MM.isHomogeneous_differential)
    MM.differential_comp_self_eq_zero

/-- The higher part is a perturbation of the unary part: `(D₀ + δ)² = D₀²`, since `D₀ + δ` is the
bar differential and both sides vanish. -/
theorem unaryBarDifferential_add_higherBarDifferential_comp_self :
    (unaryBarDifferential AA BB MM.grading MM.differential + MM.higherBarDifferential) ∘ₗ
        (unaryBarDifferential AA BB MM.grading MM.differential + MM.higherBarDifferential) =
      unaryBarDifferential AA BB MM.grading MM.differential ∘ₗ
        unaryBarDifferential AA BB MM.grading MM.differential := by
  rw [unaryBarDifferential_add_higherBarDifferential, barDifferential_sq,
    MM.unaryBarDifferential_differential_comp_self]

/-- The unit hypothesis of the perturbation lemma for the bar contraction. -/
theorem isUnit_one_add_higherBarDifferential_mul_barContraction_homotopy :
    IsUnit (1 + MM.higherBarDifferential * (MM.barContraction c hh hincl hproj).homotopy) := by
  rw [barContraction_homotopy]
  exact MM.isUnit_one_add_higherBarDifferential_mul c.homotopy

/-- The perturbation operator `X = (1 + δ (τ ⊗ h ⊗ 1))⁻¹ δ` commutes with the right coaction,
since `δ` and `τ ⊗ h ⊗ 1` do. -/
theorem coact_comp_perturbationSeries :
    Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) ∘ₗ
        (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential =
      ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential).rTensor
          (TensorWords R B) ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R B)
          (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) := by
  -- Package `δ`, and hence `1 + δ (τ ⊗ h ⊗ 1)`, its inverse and `X`, as comodule morphisms.
  let δ : Comodule.Hom R (TensorWords R B) ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :=
    ⟨MM.higherBarDifferential, MM.coact_comp_higherBarDifferential.symm⟩
  let U := Comodule.Hom.id R (TensorWords R B) ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) +
    δ.comp (Comodule.Hom.cofreeMap
      (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) c.homotopy))
  have hX := ((Comodule.Hom.ringInverse U).comp δ).map_coact_eq
  rw [Comodule.Hom.comp_toLinearMap, Comodule.Hom.ringInverse_toLinearMap] at hX
  rw [LinearSpecialContraction.perturbationSeries_def, barContraction_homotopy]
  exact hX.symm

/-- The perturbation operator is an odd map of left comodules, since `δ` and `τ ⊗ h ⊗ 1` are. -/
theorem leftCoact_comp_perturbationSeries :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ
        (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M) := by
  set Δ := Comodule.leftCoactRTensor (TensorWords R B)
    (Comodule.leftCofreeCoact R (TensorWords R A) M)
  set U : Module.End R ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :=
    1 + MM.higherBarDifferential * (MM.barContraction c hh hincl hproj).homotopy with hUdef
  -- `U` is an even map of left comodules, hence so is its inverse.
  have hU : Δ ∘ₗ U = U.lTensor (TensorWords R A) ∘ₗ Δ := by
    have h := Comodule.comp_comp_eq_lTensor_comp_of_comp_self_eq_id
      (InternalGrading.koszulTwist_comp_self _ _)
      (leftCoact_comp_rTensor_map_koszulTwist (AA := AA) (B := B) c.homotopy)
      MM.leftCoact_comp_higherBarDifferential
    rw [hUdef, Module.End.mul_eq_comp, barContraction_homotopy, LinearMap.comp_add,
      LinearMap.lTensor_add, LinearMap.add_comp, h, Module.End.one_eq_id, LinearMap.comp_id,
      LinearMap.lTensor_id, LinearMap.id_comp]
  have hUnit : IsUnit U := MM.isUnit_one_add_higherBarDifferential_mul_barContraction_homotopy
    c hh hincl hproj
  have hinv : Δ ∘ₗ Ring.inverse U = (Ring.inverse U).lTensor (TensorWords R A) ∘ₗ Δ := by
    calc Δ ∘ₗ Ring.inverse U
        = (Ring.inverse U * U).lTensor (TensorWords R A) ∘ₗ Δ ∘ₗ Ring.inverse U := by
          rw [Ring.inverse_mul_cancel _ hUnit, Module.End.one_eq_id, LinearMap.lTensor_id,
            LinearMap.id_comp]
      _ = (Ring.inverse U).lTensor (TensorWords R A) ∘ₗ Δ ∘ₗ (U * Ring.inverse U) := by
          rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.lTensor_comp,
            LinearMap.comp_assoc, ← LinearMap.comp_assoc (Ring.inverse U) U Δ, hU,
            LinearMap.comp_assoc]
      _ = (Ring.inverse U).lTensor (TensorWords R A) ∘ₗ Δ := by
          rw [Ring.mul_inverse_cancel _ hUnit, Module.End.one_eq_id, LinearMap.comp_id]
  rw [LinearSpecialContraction.perturbationSeries_def, Module.End.mul_eq_comp,
    ← LinearMap.comp_assoc, hinv, LinearMap.comp_assoc, MM.leftCoact_comp_higherBarDifferential,
    ← LinearMap.comp_assoc, LinearMap.lTensor_comp_map]

/-- The perturbation operator vanishes on the two empty words, since the higher part does. -/
@[simp]
theorem perturbationSeries_one_tmul_tmul_one (x : M) :
    (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential
      ((1 ⊗ₜ x) ⊗ₜ (1 : TensorWords R B)) = 0 := by
  rw [LinearSpecialContraction.perturbationSeries_def, mul_apply_eq_comp,
    higherBarDifferential_one_tmul_tmul_one, map_zero]

/-- The higher part has degree one. -/
theorem isHomogeneous_higherBarDifferential :
    LinearMap.IsHomogeneous MM.higherBarDifferential (barGrading AA BB MM.grading).piece
      (barGrading AA BB MM.grading).piece 1 := by
  rw [higherBarDifferential_def]
  exact MM.isHomogeneous_barDifferential.sub
    (isHomogeneous_unaryBarDifferential AA BB MM.grading
      (LinearMap.isHomogeneous_shift_piece_iff.2 MM.isHomogeneous_differential))

/-- The perturbation operator has degree one. -/
theorem isHomogeneous_perturbationSeries :
    LinearMap.IsHomogeneous
      ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential)
      (barGrading AA BB MM.grading).piece (barGrading AA BB MM.grading).piece 1 := by
  have hK := isHomogeneous_rTensor_of_leftGrading (BB := BB)
    (isHomogeneous_map_koszulTwist_leftGrading (AA := AA) hh)
  have hδK : LinearMap.IsHomogeneous
      (MM.higherBarDifferential * (MM.barContraction c hh hincl hproj).homotopy)
      (barGrading AA BB MM.grading).piece (barGrading AA BB MM.grading).piece 0 := by
    rw [Module.End.mul_eq_comp, barContraction_homotopy]
    simpa using MM.isHomogeneous_higherBarDifferential.comp hK
  have hinv := hδK.ringInverse_one_add fun z ↦ by
    rw [Module.End.mul_eq_comp, barContraction_homotopy]
    exact MM.exists_pow_higherBarDifferential_comp_apply_eq_zero c.homotopy z
  rw [LinearSpecialContraction.perturbationSeries_def, Module.End.mul_eq_comp]
  simpa only [add_zero] using hinv.comp MM.isHomogeneous_higherBarDifferential

/-! ### The transferred bimodule -/

/-- The **transferred bar differential**: the perturbed differential
`D' = D₀' + (1 ⊗ p ⊗ 1) X (1 ⊗ i ⊗ 1)` of `Tᶜ(sA) ⊗ sN ⊗ Tᶜ(sB)`, obtained from the bar
contraction by perturbing along the higher part of the bimodule bar differential. -/
noncomputable def transferBarDifferential :
    (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B →ₗ[R]
      (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B :=
  (MM.barContraction c hh hincl hproj).perturbedDifferential MM.higherBarDifferential

/-- The transferred bar differential is `D₀' + (1 ⊗ p ⊗ 1) X (1 ⊗ i ⊗ 1)`. -/
theorem transferBarDifferential_def :
    MM.transferBarDifferential c hh hincl hproj =
      unaryBarDifferential AA BB GN dN +
        (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) ∘ₗ
          (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
            (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B) := by
  rw [transferBarDifferential, LinearSpecialContraction.perturbedDifferential_def,
    barContraction_incl, barContraction_proj]

/-- The **perturbed bar contraction**: the basic perturbation lemma applied to the bar contraction
and the higher part of the bimodule bar differential.  It is a special contraction of the bar
bicomodule of `M`, with its bar differential `D₀ + δ`, onto `Tᶜ(sA) ⊗ sN ⊗ Tᶜ(sB)` with the
transferred bar differential. -/
noncomputable def transferContraction :
    LinearSpecialContraction
      (unaryBarDifferential AA BB MM.grading MM.differential + MM.higherBarDifferential)
      (MM.transferBarDifferential c hh hincl hproj) :=
  (MM.barContraction c hh hincl hproj).perturb MM.higherBarDifferential
    MM.unaryBarDifferential_add_higherBarDifferential_comp_self
    (MM.isUnit_one_add_higherBarDifferential_mul_barContraction_homotopy c hh hincl hproj)

/-- The inclusion of the perturbed bar contraction is
`i' = 1 ⊗ i ⊗ 1 - (τ ⊗ h ⊗ 1) X (1 ⊗ i ⊗ 1)`. -/
theorem transferContraction_incl :
    (MM.transferContraction c hh hincl hproj).incl =
      (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B) -
        (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
            c.homotopy).rTensor (TensorWords R B) ∘ₗ
          (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
            (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B) := by
  rw [transferContraction, LinearSpecialContraction.perturb_incl, barContraction_incl,
    barContraction_homotopy]

/-- The projection of the perturbed bar contraction is
`p' = 1 ⊗ p ⊗ 1 - (1 ⊗ p ⊗ 1) X (τ ⊗ h ⊗ 1)`. -/
theorem transferContraction_proj :
    (MM.transferContraction c hh hincl hproj).proj =
      (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) -
        (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) ∘ₗ
          (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
            (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
              c.homotopy).rTensor (TensorWords R B) := by
  rw [transferContraction, LinearSpecialContraction.perturb_proj, barContraction_proj,
    barContraction_homotopy]

/-- The perturbed inclusion commutes with the right coactions. -/
theorem coact_comp_transferContraction_incl :
    Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) ∘ₗ
        (MM.transferContraction c hh hincl hproj).incl =
      (MM.transferContraction c hh hincl hproj).incl.rTensor (TensorWords R B) ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R B)
          (M := (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) := by
  refine LinearMap.ext fun z ↦ ?_
  have hi := LinearMap.congr_fun (Comodule.Hom.cofreeMap (C := TensorWords R B)
    (c.incl.lTensor (TensorWords R A))).map_coact_eq.symm
  have hh' := LinearMap.congr_fun (Comodule.Hom.cofreeMap (C := TensorWords R B)
    (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
      c.homotopy)).map_coact_eq.symm
  have hX := LinearMap.congr_fun (MM.coact_comp_perturbationSeries c hh hincl hproj)
  simp only [LinearMap.comp_apply, Comodule.Hom.cofreeMap_toLinearMap, ← LinearMap.rTensor_def]
    at hi hh' hX
  simp only [transferContraction_incl, LinearMap.comp_apply, LinearMap.sub_apply, map_sub,
    LinearMap.rTensor_sub, hi, hh', hX, LinearMap.rTensor_comp_apply]

/-- The perturbed projection commutes with the right coactions. -/
theorem coact_comp_transferContraction_proj :
    Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) ∘ₗ
        (MM.transferContraction c hh hincl hproj).proj =
      (MM.transferContraction c hh hincl hproj).proj.rTensor (TensorWords R B) ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R B)
          (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) := by
  refine LinearMap.ext fun z ↦ ?_
  have hp := LinearMap.congr_fun (Comodule.Hom.cofreeMap (C := TensorWords R B)
    (c.proj.lTensor (TensorWords R A))).map_coact_eq.symm
  have hh' := LinearMap.congr_fun (Comodule.Hom.cofreeMap (C := TensorWords R B)
    (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
      c.homotopy)).map_coact_eq.symm
  have hX := LinearMap.congr_fun (MM.coact_comp_perturbationSeries c hh hincl hproj)
  simp only [LinearMap.comp_apply, Comodule.Hom.cofreeMap_toLinearMap, ← LinearMap.rTensor_def]
    at hp hh' hX
  simp only [transferContraction_proj, LinearMap.comp_apply, LinearMap.sub_apply, map_sub,
    LinearMap.rTensor_sub, hp, hh', hX, LinearMap.rTensor_comp_apply]

/-- The perturbed inclusion is a map of left comodules. -/
theorem leftCoact_comp_transferContraction_incl :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ
        (MM.transferContraction c hh hincl hproj).incl =
      (MM.transferContraction c hh hincl hproj).incl.lTensor (TensorWords R A) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) N) := by
  have hi := leftCoact_comp_rTensor_lTensor (A := A) (B := B) c.incl
  have hXi : Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ
        (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
          (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B) =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
            (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B)) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) N) := by
    rw [← LinearMap.comp_assoc, MM.leftCoact_comp_perturbationSeries, LinearMap.comp_assoc, hi,
      ← LinearMap.comp_assoc, LinearMap.map_comp_lTensor]
  have hhXi := Comodule.comp_comp_eq_lTensor_comp_of_comp_self_eq_id
    (InternalGrading.koszulTwist_comp_self _ _) hXi
    (leftCoact_comp_rTensor_map_koszulTwist (AA := AA) (B := B) c.homotopy)
  rw [transferContraction_incl, LinearMap.comp_sub, hi, hhXi, LinearMap.lTensor_sub]
  exact (LinearMap.sub_comp _ _ _).symm

/-- The perturbed projection is a map of left comodules. -/
theorem leftCoact_comp_transferContraction_proj :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ
        (MM.transferContraction c hh hincl hproj).proj =
      (MM.transferContraction c hh hincl hproj).proj.lTensor (TensorWords R A) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M) := by
  have hp := leftCoact_comp_rTensor_lTensor (A := A) (B := B) c.proj
  have hXh := Comodule.comp_comp_eq_lTensor_comp_of_comp_self_eq_id
    (InternalGrading.koszulTwist_comp_self _ _)
    (leftCoact_comp_rTensor_map_koszulTwist (AA := AA) (B := B) c.homotopy)
    (MM.leftCoact_comp_perturbationSeries c hh hincl hproj)
  rw [transferContraction_proj, LinearMap.comp_sub, hp, ← LinearMap.comp_assoc, hp,
    LinearMap.comp_assoc, hXh, ← LinearMap.comp_assoc, ← LinearMap.lTensor_comp,
    LinearMap.lTensor_sub]
  exact (LinearMap.sub_comp _ _ _).symm

/-- The transferred bar differential is a coderivation over the bar differential of `A` for the
left coaction: it is the unary part for `d_N` plus the odd map of left comodules
`(1 ⊗ p ⊗ 1) X (1 ⊗ i ⊗ 1)`. -/
theorem isLeftGradedCoderivationOver_transferBarDifferential :
    Comodule.IsLeftGradedCoderivationOver
      (Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N))
      (TensorWords.grading (AA.grading.shift 1)) 1 AA.coaugmentedBarDifferential
      (MM.transferBarDifferential c hh hincl hproj) := by
  have hp := leftCoact_comp_rTensor_lTensor (A := A) (B := B) c.proj
  have hi := leftCoact_comp_rTensor_lTensor (A := A) (B := B) c.incl
  have hpXi : Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ
        (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) ∘ₗ
          (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
            (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B) =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          ((c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) ∘ₗ
            (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
              (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B)) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) N) := by
    have key :
      ((c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B)).lTensor (TensorWords R A) ∘ₗ
          TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
            ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential) ∘ₗ
          ((c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B)).lTensor
            (TensorWords R A) =
        TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          ((c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) ∘ₗ
            (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
              (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B)) := by
      rw [← LinearMap.comp_assoc, LinearMap.lTensor_comp_map, LinearMap.map_comp_lTensor,
        LinearMap.comp_assoc]
    have hX := LinearMap.congr_fun (MM.leftCoact_comp_perturbationSeries c hh hincl hproj)
    have hp' := LinearMap.congr_fun hp
    have hi' := LinearMap.congr_fun hi
    have key := LinearMap.congr_fun key
    refine LinearMap.ext fun z ↦ ?_
    simp only [LinearMap.comp_apply] at key hX hp' hi' ⊢
    rw [hp', hX, hi', key]
  have hD := (isLeftGradedCoderivationOver_unaryBarDifferential AA BB GN dN).coact_apply
  rw [Comodule.isLeftGradedCoderivationOver_iff_coact_apply]
  intro z
  have hz := LinearMap.congr_fun hpXi z
  simp only [LinearMap.comp_apply] at hz
  simp only [transferBarDifferential_def, LinearMap.add_apply, map_add, hD,
    TensorProduct.map_add_right, LinearMap.comp_apply, hz]
  abel

/-- The transferred bar differential is a coderivation over the bar differential of `B` for the
right coaction: it is the unary part for `d_N` plus the comodule morphism
`(1 ⊗ p ⊗ 1) X (1 ⊗ i ⊗ 1)`. -/
theorem isGradedCoderivationOver_transferBarDifferential :
    Comodule.IsGradedCoderivationOver (barGrading AA BB GN) 1 BB.coaugmentedBarDifferential
      (MM.transferBarDifferential c hh hincl hproj) := by
  have hp := LinearMap.congr_fun (Comodule.Hom.cofreeMap (C := TensorWords R B)
    (c.proj.lTensor (TensorWords R A))).map_coact_eq.symm
  have hi := LinearMap.congr_fun (Comodule.Hom.cofreeMap (C := TensorWords R B)
    (c.incl.lTensor (TensorWords R A))).map_coact_eq.symm
  have hX := LinearMap.congr_fun (MM.coact_comp_perturbationSeries c hh hincl hproj)
  have hD := (isGradedCoderivationOver_unaryBarDifferential AA BB GN dN).coact_apply
  simp only [LinearMap.comp_apply, Comodule.Hom.cofreeMap_toLinearMap, ← LinearMap.rTensor_def]
    at hp hi hX
  rw [Comodule.isGradedCoderivationOver_iff_coact_apply]
  intro z
  simp only [transferBarDifferential_def, LinearMap.add_apply, LinearMap.comp_apply, map_add, hD,
    hp, hi, hX, LinearMap.rTensor_add, LinearMap.rTensor_comp_apply]
  abel

/-- The transferred bar differential squares to zero. -/
@[simp]
theorem transferBarDifferential_comp_self :
    MM.transferBarDifferential c hh hincl hproj ∘ₗ MM.transferBarDifferential c hh hincl hproj =
      0 :=
  LinearSpecialContraction.perturbedDifferential_comp_perturbedDifferential_eq_zero _ _
    MM.unaryBarDifferential_add_higherBarDifferential_comp_self
    MM.unaryBarDifferential_differential_comp_self

include hincl hproj in
/-- The differential of the retract has degree one for the suspended grading. -/
private theorem isHomogeneous_dN_shift :
    LinearMap.IsHomogeneous dN (GN.shift 1).piece (GN.shift 1).piece 1 :=
  LinearMap.isHomogeneous_shift_piece_iff.2 <| c.isHomogeneous_dN MM.isHomogeneous_differential
    hincl hproj

/-- The transferred bar differential has degree one. -/
theorem isHomogeneous_transferBarDifferential :
    LinearMap.IsHomogeneous (MM.transferBarDifferential c hh hincl hproj)
      (barGrading AA BB GN).piece (barGrading AA BB GN).piece 1 := by
  rw [transferBarDifferential_def]
  have hpXi := (isHomogeneous_rTensor_of_leftGrading (BB := BB)
    (isHomogeneous_lTensor_leftGrading (AA := AA) hproj)).comp
    ((MM.isHomogeneous_perturbationSeries c hh hincl hproj).comp
      (isHomogeneous_rTensor_of_leftGrading (BB := BB)
        (isHomogeneous_lTensor_leftGrading (AA := AA) hincl)))
  simpa only [zero_add, add_zero] using
    (isHomogeneous_unaryBarDifferential AA BB GN (MM.isHomogeneous_dN_shift c hincl hproj)).add
      hpXi

/-- The **transferred `A∞` bimodule** on the retract `N` of a special contraction of `(M, m₁)`:
its bar differential is the transferred bar differential. -/
noncomputable def transfer : AInfinityBimodule AA BB N :=
  ofBarDifferential GN (MM.transferBarDifferential c hh hincl hproj)
    (MM.isHomogeneous_transferBarDifferential c hh hincl hproj)
    (MM.isLeftGradedCoderivationOver_transferBarDifferential c hh hincl hproj)
    (MM.isGradedCoderivationOver_transferBarDifferential c hh hincl hproj)
    (by rw [transferBarDifferential_comp_self, LinearMap.comp_zero])

/-- The transferred bimodule lives on the grading of the retract. -/
@[simp]
theorem transfer_grading : (MM.transfer c hh hincl hproj).grading = GN :=
  ofBarDifferential_grading ..

/-- The bar differential of the transferred bimodule is the transferred bar differential. -/
@[simp]
theorem barDifferential_transfer :
    (MM.transfer c hh hincl hproj).barDifferential = MM.transferBarDifferential c hh hincl hproj :=
  ofBarDifferential_barDifferential ..

/-- The unary operation of the transferred bimodule is the differential of the retract. -/
@[simp]
theorem differential_transfer : (MM.transfer c hh hincl hproj).differential = dN := by
  ext y
  rw [differential_apply, taylor_apply, barDifferential_transfer, transferBarDifferential_def]
  simp [AA.coaugmentedBarDifferential_one, BB.coaugmentedBarDifferential_one, TensorWords.map_one,
    TensorWords.counit_eq_counit, TensorWords.counit_one]

/-! ### The extending and projecting morphisms -/

/-- The perturbed inclusion has degree zero. -/
theorem isHomogeneous_transferContraction_incl :
    LinearMap.IsHomogeneous (MM.transferContraction c hh hincl hproj).incl
      (barGrading AA BB GN).piece (barGrading AA BB MM.grading).piece 0 := by
  rw [transferContraction_incl]
  have hi := isHomogeneous_rTensor_of_leftGrading (BB := BB)
    (isHomogeneous_lTensor_leftGrading (AA := AA) hincl)
  have hhXi := (isHomogeneous_rTensor_of_leftGrading (BB := BB)
    (isHomogeneous_map_koszulTwist_leftGrading (AA := AA) hh)).comp
    ((MM.isHomogeneous_perturbationSeries c hh hincl hproj).comp hi)
  simpa only [zero_add, add_neg_cancel] using hi.sub hhXi

/-- The perturbed projection has degree zero. -/
theorem isHomogeneous_transferContraction_proj :
    LinearMap.IsHomogeneous (MM.transferContraction c hh hincl hproj).proj
      (barGrading AA BB MM.grading).piece (barGrading AA BB GN).piece 0 := by
  rw [transferContraction_proj]
  have hp := isHomogeneous_rTensor_of_leftGrading (BB := BB)
    (isHomogeneous_lTensor_leftGrading (AA := AA) hproj)
  have hpXh := hp.comp ((MM.isHomogeneous_perturbationSeries c hh hincl hproj).comp
    (isHomogeneous_rTensor_of_leftGrading (BB := BB)
      (isHomogeneous_map_koszulTwist_leftGrading (AA := AA) hh)))
  simpa only [zero_add, neg_add_cancel] using hp.sub hpXh

/-- The **extending morphism** of `A∞` bimodules from the transferred bimodule to `M`: its bar map
is the perturbed inclusion `i' = 1 ⊗ i ⊗ 1 - (τ ⊗ h ⊗ 1) X (1 ⊗ i ⊗ 1)`. -/
noncomputable def transferInclusion :
    AInfinityBimoduleHom (MM.transfer c hh hincl hproj) MM where
  barHom := ⟨(MM.transferContraction c hh hincl hproj).incl,
    (MM.coact_comp_transferContraction_incl c hh hincl hproj).symm⟩
  leftCoact_comp_barMap := MM.leftCoact_comp_transferContraction_incl c hh hincl hproj
  isHomogeneous_barMap := by
    rw [transfer_grading]
    exact MM.isHomogeneous_transferContraction_incl c hh hincl hproj
  barDifferential_comp_barMap := by
    rw [barDifferential_transfer, ← unaryBarDifferential_add_higherBarDifferential]
    exact (MM.transferContraction c hh hincl hproj).dM_comp_incl

/-- The bar map of the extending morphism is the perturbed inclusion. -/
@[simp]
theorem barMap_transferInclusion :
    (MM.transferInclusion c hh hincl hproj).barMap =
      (MM.transferContraction c hh hincl hproj).incl :=
  (rfl)

/-- The **projecting morphism** of `A∞` bimodules from `M` to the transferred bimodule: its bar
map is the perturbed projection `p' = 1 ⊗ p ⊗ 1 - (1 ⊗ p ⊗ 1) X (τ ⊗ h ⊗ 1)`. -/
noncomputable def transferProjection :
    AInfinityBimoduleHom MM (MM.transfer c hh hincl hproj) where
  barHom := ⟨(MM.transferContraction c hh hincl hproj).proj,
    (MM.coact_comp_transferContraction_proj c hh hincl hproj).symm⟩
  leftCoact_comp_barMap := MM.leftCoact_comp_transferContraction_proj c hh hincl hproj
  isHomogeneous_barMap := by
    rw [transfer_grading]
    exact MM.isHomogeneous_transferContraction_proj c hh hincl hproj
  barDifferential_comp_barMap := by
    rw [barDifferential_transfer, ← unaryBarDifferential_add_higherBarDifferential]
    exact (MM.transferContraction c hh hincl hproj).proj_comp_dM.symm

/-- The bar map of the projecting morphism is the perturbed projection. -/
@[simp]
theorem barMap_transferProjection :
    (MM.transferProjection c hh hincl hproj).barMap =
      (MM.transferContraction c hh hincl hproj).proj :=
  (rfl)

/-- The linear part of the extending morphism is the inclusion of the contraction. -/
@[simp]
theorem linearPart_transferInclusion :
    (MM.transferInclusion c hh hincl hproj).linearPart = c.incl := by
  ext y
  simp [AInfinityBimoduleHom.linearPart_apply, AInfinityBimoduleHom.taylor_def,
    transferContraction_incl, TensorWords.counit_eq_counit, TensorWords.counit_one]

/-- The linear part of the projecting morphism is the projection of the contraction. -/
@[simp]
theorem linearPart_transferProjection :
    (MM.transferProjection c hh hincl hproj).linearPart = c.proj := by
  ext x
  simp [AInfinityBimoduleHom.linearPart_apply, AInfinityBimoduleHom.taylor_def,
    transferContraction_proj, TensorWords.map_one, TensorWords.counit_eq_counit,
    TensorWords.counit_one]

/-- The projecting morphism is a left inverse of the extending morphism. -/
@[simp]
theorem transferProjection_comp_transferInclusion :
    (MM.transferProjection c hh hincl hproj).comp (MM.transferInclusion c hh hincl hproj) =
      AInfinityBimoduleHom.id _ :=
  AInfinityBimoduleHom.barMap_injective <| by
    rw [AInfinityBimoduleHom.barMap_comp, barMap_transferProjection, barMap_transferInclusion,
      AInfinityBimoduleHom.barMap_id]
    exact (MM.transferContraction c hh hincl hproj).proj_comp_incl

/-- The extending morphism is a quasi-isomorphism: its linear part is the inclusion of a
contraction. -/
theorem isQuasiIso_transferInclusion : (MM.transferInclusion c hh hincl hproj).IsQuasiIso := by
  rw [AInfinityBimoduleHom.isQuasiIso_iff, linearPart_transferInclusion, differential_transfer]
  refine ⟨fun x _ hx ↦ ?_, fun y hy ↦ ⟨c.proj y, ?_, ?_⟩⟩
  · obtain ⟨y, hy⟩ := hx
    exact ⟨c.proj y, by rw [← c.proj_dM_apply, hy, c.proj_incl_apply]⟩
  · rw [LinearMap.mem_ker, ← c.proj_dM_apply, LinearMap.mem_ker.1 hy, map_zero]
  · rw [c.incl_proj_apply, LinearMap.mem_ker.1 hy, map_zero, sub_zero, sub_sub_cancel]
    exact ⟨c.homotopy y, rfl⟩

/-- The projecting morphism is a quasi-isomorphism. -/
theorem isQuasiIso_transferProjection : (MM.transferProjection c hh hincl hproj).IsQuasiIso :=
  (MM.isQuasiIso_transferInclusion c hh hincl hproj).of_precomp <| by
    rw [transferProjection_comp_transferInclusion]
    exact AInfinityBimoduleHom.isQuasiIso_id _

end Transfer

end AInfinityBimodule

end TauCeti
