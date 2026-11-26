/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Hom.Cohomology
import TauCeti.Algebra.Homology.Contraction.Linear.Homology.Equiv

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
of `(M, m₁)` tensored on the left with `(Tᶜ(sA), b_A)` (`TauCeti.AInfinityBimodule.leftContraction`,
via `TauCeti.LinearSpecialContraction.lTensor`), then on the right with `(Tᶜ(sB), b_B)`.  The basic
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

attribute [local instance] Comodule.cofree

/-! ### The bar contraction and the perturbation -/

section Transfer

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} (MM : AInfinityBimodule AA BB M)
  {GN : InternalGrading R N ℤ} {dN : Module.End R N}
  (c : LinearSpecialContraction MM.differential dN)
  (hh : LinearMap.IsHomogeneous c.homotopy MM.grading.piece MM.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GN.piece MM.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj MM.grading.piece GN.piece 0)

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
      (AA.leftUnaryDifferential MM.differential) (AA.leftUnaryDifferential dN) :=
  (c.lTensor AA.isHomogeneous_coaugmentedBarDifferential).copy
    (c.incl.lTensor (TensorWords R A)) (c.proj.lTensor (TensorWords R A))
    (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) c.homotopy)
    (AInfinityAlgebra.leftUnaryDifferential_def ..).symm
    (AInfinityAlgebra.leftUnaryDifferential_def ..).symm
    (LinearSpecialContraction.lTensor_incl ..) (LinearSpecialContraction.lTensor_proj ..)
    (LinearSpecialContraction.lTensor_homotopy ..)

/-- The inclusion of the left contraction is `1 ⊗ i`. -/
@[simp]
theorem leftContraction_incl :
    (MM.leftContraction c).incl = c.incl.lTensor (TensorWords R A) :=
  LinearSpecialContraction.copy_incl ..

/-- The projection of the left contraction is `1 ⊗ p`. -/
@[simp]
theorem leftContraction_proj :
    (MM.leftContraction c).proj = c.proj.lTensor (TensorWords R A) :=
  LinearSpecialContraction.copy_proj ..

/-- The homotopy of the left contraction is `τ ⊗ h`. -/
@[simp]
theorem leftContraction_homotopy :
    (MM.leftContraction c).homotopy =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) c.homotopy :=
  LinearSpecialContraction.copy_homotopy ..

include hincl in
/-- The inclusion `1 ⊗ i` of the left contraction has degree zero for the left gradings. -/
private theorem isHomogeneous_leftContraction_incl :
    LinearMap.IsHomogeneous (MM.leftContraction c).incl ((leftGrading AA GN).shift 1).piece
      ((leftGrading AA MM.grading).shift 1).piece 0 := by
  rw [leftContraction_incl, shift_one_leftGrading, shift_one_leftGrading]
  simpa only [LinearContraction.lTensor_incl] using
    c.isHomogeneous_lTensor_incl AA.isHomogeneous_coaugmentedBarDifferential
      (LinearMap.isHomogeneous_shift_piece_iff.2 hincl)

include hproj in
/-- The projection `1 ⊗ p` of the left contraction has degree zero for the left gradings. -/
private theorem isHomogeneous_leftContraction_proj :
    LinearMap.IsHomogeneous (MM.leftContraction c).proj ((leftGrading AA MM.grading).shift 1).piece
      ((leftGrading AA GN).shift 1).piece 0 := by
  rw [leftContraction_proj, shift_one_leftGrading, shift_one_leftGrading]
  simpa only [LinearContraction.lTensor_proj] using
    c.isHomogeneous_lTensor_proj AA.isHomogeneous_coaugmentedBarDifferential
      (LinearMap.isHomogeneous_shift_piece_iff.2 hproj)

include hh in
/-- The homotopy `τ ⊗ h` of the left contraction has degree minus one for the left grading. -/
private theorem isHomogeneous_leftContraction_homotopy :
    LinearMap.IsHomogeneous (MM.leftContraction c).homotopy
      ((leftGrading AA MM.grading).shift 1).piece ((leftGrading AA MM.grading).shift 1).piece
      (-1) := by
  rw [leftContraction_homotopy, shift_one_leftGrading]
  simpa only [LinearContraction.lTensor_homotopy] using
    c.isHomogeneous_lTensor_homotopy AA.isHomogeneous_coaugmentedBarDifferential
      (LinearMap.isHomogeneous_shift_piece_iff.2 hh)

/-- The **bar contraction**: a special contraction of `(M, m₁)` onto `(N, d_N)` induces the
special contraction `(1 ⊗ i ⊗ 1, 1 ⊗ p ⊗ 1, τ ⊗ h ⊗ 1)` of the bar bicomodules
`Tᶜ(sA) ⊗ sM ⊗ Tᶜ(sB)` onto `Tᶜ(sA) ⊗ sN ⊗ Tᶜ(sB)` for the unary parts of the bar
differentials. -/
noncomputable def barContraction :
    LinearSpecialContraction (unaryBarDifferential AA BB MM.grading MM.differential)
      (unaryBarDifferential AA BB GN dN) :=
  let c' := (MM.leftContraction c).rTensor (MM.isHomogeneous_leftContraction_homotopy c hh)
    (MM.isHomogeneous_leftContraction_incl c hincl) (MM.isHomogeneous_leftContraction_proj c hproj)
    BB.coaugmentedBarDifferential
  c'.copy c'.incl c'.proj c'.homotopy
    (unaryBarDifferential_eq_rTensor_add AA BB MM.grading MM.differential).symm
    (unaryBarDifferential_eq_rTensor_add AA BB GN dN).symm rfl rfl rfl

/-- The inclusion of the bar contraction is `1 ⊗ i ⊗ 1`. -/
@[simp]
theorem barContraction_incl :
    (MM.barContraction c hh hincl hproj).incl =
      (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B) := by
  simp only [barContraction, LinearSpecialContraction.copy_incl,
    LinearSpecialContraction.rTensor_incl, leftContraction_incl]

/-- The projection of the bar contraction is `1 ⊗ p ⊗ 1`. -/
@[simp]
theorem barContraction_proj :
    (MM.barContraction c hh hincl hproj).proj =
      (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) := by
  simp only [barContraction, LinearSpecialContraction.copy_proj,
    LinearSpecialContraction.rTensor_proj, leftContraction_proj]

/-- The homotopy of the bar contraction is `τ ⊗ h ⊗ 1`. -/
@[simp]
theorem barContraction_homotopy :
    (MM.barContraction c hh hincl hproj).homotopy =
      (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
        c.homotopy).rTensor (TensorWords R B) := by
  simp only [barContraction, LinearSpecialContraction.copy_homotopy,
    LinearSpecialContraction.rTensor_homotopy, leftContraction_homotopy]

/-- The bar contraction's inclusion has degree zero in the total suspended grading. -/
theorem isHomogeneous_barContraction_incl :
    LinearMap.IsHomogeneous (MM.barContraction c hh hincl hproj).incl
      (barGrading AA BB GN).piece (barGrading AA BB MM.grading).piece 0 := by
  have h := MM.isHomogeneous_leftContraction_incl c hincl
  rw [leftContraction_incl] at h
  rw [barContraction_incl]
  exact isHomogeneous_rTensor_of_leftGrading h

/-- The bar contraction's projection has degree zero in the total suspended grading. -/
theorem isHomogeneous_barContraction_proj :
    LinearMap.IsHomogeneous (MM.barContraction c hh hincl hproj).proj
      (barGrading AA BB MM.grading).piece (barGrading AA BB GN).piece 0 := by
  have h := MM.isHomogeneous_leftContraction_proj c hproj
  rw [leftContraction_proj] at h
  rw [barContraction_proj]
  exact isHomogeneous_rTensor_of_leftGrading h

/-- The bar contraction's homotopy has degree minus one in the total suspended grading. -/
theorem isHomogeneous_barContraction_homotopy :
    LinearMap.IsHomogeneous (MM.barContraction c hh hincl hproj).homotopy
      (barGrading AA BB MM.grading).piece (barGrading AA BB MM.grading).piece (-1) := by
  have h := MM.isHomogeneous_leftContraction_homotopy c hh
  rw [leftContraction_homotopy] at h
  rw [barContraction_homotopy]
  exact isHomogeneous_rTensor_of_leftGrading h

/-- The unit hypothesis of the perturbation lemma for the bar contraction. -/
theorem isUnit_one_add_higherBarDifferential_mul_barContraction_homotopy :
    IsUnit (1 + MM.higherBarDifferential * (MM.barContraction c hh hincl hproj).homotopy) := by
  rw [barContraction_homotopy]
  exact MM.isUnit_one_add_higherBarDifferential_mul_rTensor_map c.homotopy

/-- The perturbation operator `X = (1 + δ (τ ⊗ h ⊗ 1))⁻¹ δ` commutes with the right coaction,
since `δ` and `τ ⊗ h ⊗ 1` do. -/
theorem coact_comp_perturbationSeries :
    Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) ∘ₗ
        (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential =
      ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential).rTensor
          (TensorWords R B) ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R B)
          (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :=
  (MM.barContraction c hh hincl hproj).comp_perturbationSeries_eq_rTensor_comp
    (MM.isUnit_one_add_higherBarDifferential_mul_barContraction_homotopy c hh hincl hproj)
    MM.coact_comp_higherBarDifferential
    (by rw [barContraction_homotopy]; exact (Comodule.Hom.cofreeMap _).map_coact_eq.symm)

/-- The perturbation operator is an odd map of left comodules, since `δ` and `τ ⊗ h ⊗ 1` are. -/
theorem leftCoact_comp_perturbationSeries :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ
        (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M) :=
  (MM.barContraction c hh hincl hproj).comp_perturbationSeries_eq_map_comp
    (MM.isUnit_one_add_higherBarDifferential_mul_barContraction_homotopy c hh hincl hproj)
    (InternalGrading.koszulTwist_comp_self _ _) MM.leftCoact_comp_higherBarDifferential
    (by rw [barContraction_homotopy]; exact leftCoact_comp_rTensor_map_koszulTwist c.homotopy)

/-- After a map `1 ⊗ g ⊗ 1` acting on the module input, the perturbation operator is still an odd
map of left comodules. -/
private theorem leftCoact_comp_perturbationSeries_comp_rTensor_lTensor {P : Type*}
    [AddCommMonoid P] [Module R P] (g : P →ₗ[R] M) :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ
        (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
          (g.lTensor (TensorWords R A)).rTensor (TensorWords R B) =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
            (g.lTensor (TensorWords R A)).rTensor (TensorWords R B)) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) P) := by
  have hg := leftCoact_comp_rTensor_lTensor (A := A) (B := B) g
  rw [LinearMap.lTensor_def (M := TensorWords R A)
    (f := (g.lTensor (TensorWords R A)).rTensor (TensorWords R B))] at hg
  rw [Comodule.comp_comp_eq_map_comp_comp hg
    (MM.leftCoact_comp_perturbationSeries c hh hincl hproj), LinearMap.comp_id]

/-- The perturbation operator vanishes on the two empty words, since the higher part does. -/
@[simp]
theorem perturbationSeries_one_tmul_tmul_one (x : M) :
    (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential
      ((1 ⊗ₜ x) ⊗ₜ (1 : TensorWords R B)) = 0 := by
  rw [LinearSpecialContraction.perturbationSeries_def, mul_apply_eq_comp,
    higherBarDifferential_one_tmul_tmul_one, map_zero]

/-- The perturbation operator has degree one. -/
theorem isHomogeneous_perturbationSeries :
    LinearMap.IsHomogeneous
      ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential)
      (barGrading AA BB MM.grading).piece (barGrading AA BB MM.grading).piece 1 :=
  (MM.barContraction c hh hincl hproj).isHomogeneous_perturbationSeries
    MM.isHomogeneous_higherBarDifferential
    (MM.isHomogeneous_barContraction_homotopy c hh hincl hproj) fun z ↦ by
      rw [Module.End.mul_eq_comp, barContraction_homotopy]
      exact MM.exists_pow_higherBarDifferential_comp_rTensor_map_apply_eq_zero c.homotopy z

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
  rw [transferContraction]
  exact (MM.barContraction c hh hincl hproj).comp_perturb_incl_eq_rTensor_comp _ _
    MM.coact_comp_higherBarDifferential
    (by rw [barContraction_homotopy]; exact (Comodule.Hom.cofreeMap _).map_coact_eq.symm)
    (by rw [barContraction_incl]; exact (Comodule.Hom.cofreeMap _).map_coact_eq.symm)

/-- The perturbed projection commutes with the right coactions. -/
theorem coact_comp_transferContraction_proj :
    Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) ∘ₗ
        (MM.transferContraction c hh hincl hproj).proj =
      (MM.transferContraction c hh hincl hproj).proj.rTensor (TensorWords R B) ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R B)
          (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) := by
  rw [transferContraction]
  exact (MM.barContraction c hh hincl hproj).comp_perturb_proj_eq_rTensor_comp _ _
    MM.coact_comp_higherBarDifferential
    (by rw [barContraction_homotopy]; exact (Comodule.Hom.cofreeMap _).map_coact_eq.symm)
    (by rw [barContraction_proj]; exact (Comodule.Hom.cofreeMap _).map_coact_eq.symm)

/-- The perturbed inclusion is a map of left comodules. -/
theorem leftCoact_comp_transferContraction_incl :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ
        (MM.transferContraction c hh hincl hproj).incl =
      (MM.transferContraction c hh hincl hproj).incl.lTensor (TensorWords R A) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) N) := by
  rw [transferContraction]
  exact (MM.barContraction c hh hincl hproj).comp_perturb_incl_eq_lTensor_comp _ _
    (InternalGrading.koszulTwist_comp_self _ _) MM.leftCoact_comp_higherBarDifferential
    (by rw [barContraction_homotopy]; exact leftCoact_comp_rTensor_map_koszulTwist c.homotopy)
    (by rw [barContraction_incl]; exact leftCoact_comp_rTensor_lTensor c.incl)

/-- The perturbed projection is a map of left comodules. -/
theorem leftCoact_comp_transferContraction_proj :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ
        (MM.transferContraction c hh hincl hproj).proj =
      (MM.transferContraction c hh hincl hproj).proj.lTensor (TensorWords R A) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M) := by
  rw [transferContraction]
  exact (MM.barContraction c hh hincl hproj).comp_perturb_proj_eq_lTensor_comp _ _
    (InternalGrading.koszulTwist_comp_self _ _) MM.leftCoact_comp_higherBarDifferential
    (by rw [barContraction_homotopy]; exact leftCoact_comp_rTensor_map_koszulTwist c.homotopy)
    (by rw [barContraction_proj]; exact leftCoact_comp_rTensor_lTensor c.proj)

/-- The transferred bar differential is a coderivation over the bar differential of `A` for the
left coaction: it is the unary part for `d_N` plus the odd map of left comodules
`(1 ⊗ p ⊗ 1) X (1 ⊗ i ⊗ 1)`. -/
theorem isLeftGradedCoderivationOver_transferBarDifferential :
    Comodule.IsLeftGradedCoderivationOver
      (Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N))
      (TensorWords.grading (AA.grading.shift 1)) 1 AA.coaugmentedBarDifferential
      (MM.transferBarDifferential c hh hincl hproj) := by
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
    have hp := leftCoact_comp_rTensor_lTensor (A := A) (B := B) c.proj
    rw [LinearMap.lTensor_def (M := TensorWords R A)
      (f := (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B))] at hp
    rw [Comodule.comp_comp_eq_map_comp_comp
      (MM.leftCoact_comp_perturbationSeries_comp_rTensor_lTensor c hh hincl hproj c.incl) hp,
      LinearMap.id_comp]
  rw [transferBarDifferential_def]
  exact (isLeftGradedCoderivationOver_unaryBarDifferential AA BB GN dN).add_of_comp_eq_map_comp
    hpXi

/-- The transferred bar differential is a coderivation over the bar differential of `B` for the
right coaction: it is the unary part for `d_N` plus the comodule morphism
`(1 ⊗ p ⊗ 1) X (1 ⊗ i ⊗ 1)`. -/
theorem isGradedCoderivationOver_transferBarDifferential :
    Comodule.IsGradedCoderivationOver (barGrading AA BB GN) 1 BB.coaugmentedBarDifferential
      (MM.transferBarDifferential c hh hincl hproj) := by
  have hp := (Comodule.Hom.cofreeMap (C := TensorWords R B)
    (c.proj.lTensor (TensorWords R A))).map_coact_apply
  have hi := (Comodule.Hom.cofreeMap (C := TensorWords R B)
    (c.incl.lTensor (TensorWords R A))).map_coact_apply
  have hX := LinearMap.congr_fun (MM.coact_comp_perturbationSeries c hh hincl hproj)
  simp only [Comodule.Hom.cofreeMap_toLinearMap, Comodule.Hom.cofreeMap_apply,
    ← LinearMap.rTensor_def] at hp hi
  simp only [LinearMap.comp_apply] at hX
  rw [transferBarDifferential_def]
  refine (isGradedCoderivationOver_unaryBarDifferential AA BB GN dN).add_of_coact_comp
    (LinearMap.ext fun z ↦ ?_)
  simp only [LinearMap.comp_apply, ← hp, ← hi, hX, LinearMap.rTensor_comp_apply]

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
  rw [transferBarDifferential]
  exact (MM.barContraction c hh hincl hproj).isHomogeneous_perturbedDifferential
    (MM.isHomogeneous_barContraction_incl c hh hincl hproj)
    (MM.isHomogeneous_barContraction_proj c hh hincl hproj)
    (MM.isHomogeneous_perturbationSeries c hh hincl hproj)
    (isHomogeneous_unaryBarDifferential AA BB GN (MM.isHomogeneous_dN_shift c hincl hproj))

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
  rw [transferContraction]
  exact (MM.barContraction c hh hincl hproj).isHomogeneous_perturb_incl
    (MM.isHomogeneous_barContraction_incl c hh hincl hproj)
    (MM.isHomogeneous_barContraction_homotopy c hh hincl hproj)
    (MM.isHomogeneous_perturbationSeries c hh hincl hproj) _ _

/-- The perturbed projection has degree zero. -/
theorem isHomogeneous_transferContraction_proj :
    LinearMap.IsHomogeneous (MM.transferContraction c hh hincl hproj).proj
      (barGrading AA BB MM.grading).piece (barGrading AA BB GN).piece 0 := by
  rw [transferContraction]
  exact (MM.barContraction c hh hincl hproj).isHomogeneous_perturb_proj
    (MM.isHomogeneous_barContraction_proj c hh hincl hproj)
    (MM.isHomogeneous_barContraction_homotopy c hh hincl hproj)
    (MM.isHomogeneous_perturbationSeries c hh hincl hproj) _ _

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
  exact ⟨fun _ _ hx ↦ c.mem_range_of_incl_mem_range hx,
    fun _ hy ↦ c.exists_mem_ker_sub_incl_mem_range hy⟩

/-- The projecting morphism is a quasi-isomorphism. -/
theorem isQuasiIso_transferProjection : (MM.transferProjection c hh hincl hproj).IsQuasiIso :=
  (MM.isQuasiIso_transferInclusion c hh hincl hproj).of_precomp <| by
    rw [transferProjection_comp_transferInclusion]
    exact AInfinityBimoduleHom.isQuasiIso_id _

end Transfer

end AInfinityBimodule

end TauCeti
