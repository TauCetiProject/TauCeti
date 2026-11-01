/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Inverse
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Cohomology
public import TauCeti.Algebra.Homology.Contraction.Linear.TensorProduct
public import TauCeti.Algebra.Homology.Contraction.Perturbation
public import TauCeti.LinearAlgebra.End.LocallyNilpotent

/-!
# Homological transfer of right A-infinity modules

Let `M` be a right `A∞` module over an `A∞` algebra `A`, and let `(i, p, h)` be a special
contraction of `(M, m₁)` onto a graded module `(N, d_N)`, with `h` of degree `-1` and `i`, `p` of
degree zero.  The module is stored on its cofree bar comodule `sM ⊗ Tᶜ(sA)` by a square-zero
coderivation `D` over the bar differential `b` of `A`.  Split it as `D = D₀ + δ`, where

`D₀ = m₁ ⊗ 1 + (1 ⊗ b) ∘ (τ ⊗ 1)`

(`TauCeti.AInfinityRightModule.unaryBarDifferential`) only involves the unary module operation,
with `τ` the Koszul twist of `sM`, and the *higher* part `δ`
(`TauCeti.AInfinityRightModule.higherBarDifferential`) applies the module operations with at least
one algebra input to the prefixes of a word.  Thus `δ` strictly lowers the length of the algebra
word, and, unlike `D₀`, it is a morphism of comodules.

Tensoring the contraction with `(Tᶜ(sA), b)` gives the special contraction
`(i ⊗ 1, p ⊗ 1, h ⊗ 1)` of `(sM ⊗ Tᶜ(sA), D₀)` onto `sN ⊗ Tᶜ(sA)`
(`TauCeti.AInfinityRightModule.barContraction`), and the basic perturbation lemma transports it
along `δ`.  As `h ⊗ 1` preserves word length, `δ (h ⊗ 1)` is locally nilpotent, so the
perturbation operator `X = (1 + δ (h ⊗ 1))⁻¹ δ` exists.  Since `i ⊗ 1`, `p ⊗ 1`, `h ⊗ 1` and `δ`
are all comodule morphisms, so is `X`, and the perturbed differential `D' = D₀' + (p ⊗ 1) X (i ⊗ 1)`
of `sN ⊗ Tᶜ(sA)` is again a coderivation over `b`, squaring to zero.  It is the bar differential of
the *transferred* right `A∞` module structure on `N`
(`TauCeti.AInfinityRightModule.transfer`), whose unary operation is `d_N`.  The perturbed inclusion
`i' = i ⊗ 1 - (h ⊗ 1) X (i ⊗ 1)` and projection `p' = p ⊗ 1 - (p ⊗ 1) X (h ⊗ 1)` are comodule
morphisms intertwining the bar differentials, hence morphisms of right `A∞` modules
`TauCeti.AInfinityRightModule.transferInclusion` and
`TauCeti.AInfinityRightModule.transferProjection`, with linear parts `i` and `p`.  Both are
quasi-isomorphisms, and the projection is a left inverse of the inclusion.

The construction follows the transfer of an `A∞` algebra structure,
`TauCeti.AInfinityAlgebra.transfer` in `TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Basic`.
Unlike that case, where the tensor-trick homotopy is only a coderivation homotopy, here the
homotopy `h ⊗ 1` acts on the module input alone, so it is a comodule morphism and so is everything
built from it.  This is what makes the comodule
compatibility of the perturbed data a formal consequence of the perturbation lemma.

## Main definitions

* `TauCeti.AInfinityRightModule.unaryBarDifferential`: the part `m₁ ⊗ 1 + (1 ⊗ b)(τ ⊗ 1)` of the
  module bar differential.
* `TauCeti.AInfinityRightModule.higherBarDifferential`: the rest of the module bar differential.
* `TauCeti.AInfinityRightModule.barContraction`: the contraction of bar comodules induced by a
  contraction of the module.
* `TauCeti.AInfinityRightModule.transferBarDifferential`: the perturbed differential `D'`.
* `TauCeti.AInfinityRightModule.transferContraction`: the perturbed contraction of bar comodules,
  with inclusion `i'` and projection `p'`.
* `TauCeti.AInfinityRightModule.transfer`: the transferred right `A∞` module structure.
* `TauCeti.AInfinityRightModule.transferInclusion`: the morphism of right `A∞` modules extending
  the inclusion.
* `TauCeti.AInfinityRightModule.transferProjection`: the morphism of right `A∞` modules extending
  the projection.

## Main results

* `TauCeti.AInfinityRightModule.higherBarDifferential_tmul_of_tprod`: the higher part applies the
  higher module operations to the nonempty prefixes of a word.
* `TauCeti.AInfinityRightModule.isUnit_one_add_higherBarDifferential_mul_rTensor`: the unit
  required by the perturbation lemma.
* `TauCeti.AInfinityRightModule.barDifferential_transfer`: the bar differential of the transferred
  module is the perturbed differential.
* `TauCeti.AInfinityRightModule.differential_transfer`: the transferred unary operation is `d_N`.
* `TauCeti.AInfinityRightModule.linearPart_transferInclusion` and
  `TauCeti.AInfinityRightModule.linearPart_transferProjection`: the linear parts are `i` and `p`.
* `TauCeti.AInfinityRightModule.transferProjection_comp_transferInclusion`: the projection is a
  left inverse of the inclusion.
* `TauCeti.AInfinityRightModule.isQuasiIso_transferInclusion` and
  `TauCeti.AInfinityRightModule.isQuasiIso_transferProjection`: both are quasi-isomorphisms.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open scoped TensorProduct

universe uR uA uM uN

namespace TauCeti

open TensorWords

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

namespace AInfinityRightModule

attribute [local instance] Comodule.cofree

variable {AA : AInfinityAlgebra R A}

/-! ### The unary and higher parts of the bar differential -/

section Unary

variable (AA) (G : InternalGrading R M) (d : Module.End R M)

/-- The **unary part** `d ⊗ 1 + (1 ⊗ b) ∘ (τ ⊗ 1)` of a module bar differential with unary
operation `d`: the operator `d` on the module input, plus the algebra bar differential `b` on the
word, with the Koszul sign `τ` of moving it past the suspended module input.  For a right `A∞`
module and `d = m₁` this is the part of the bar differential which uses no higher module
operation. -/
noncomputable def unaryBarDifferential : Module.End R (M ⊗[R] TensorWords R A) :=
  d.rTensor (TensorWords R A) +
    AA.coaugmentedBarDifferential.lTensor M ∘ₗ ((G.shift 1).koszulTwist 1).rTensor (TensorWords R A)

/-- The unary part is `d ⊗ 1 + (1 ⊗ b) ∘ (τ ⊗ 1)`. -/
theorem unaryBarDifferential_def :
    unaryBarDifferential AA G d = d.rTensor (TensorWords R A) +
      AA.coaugmentedBarDifferential.lTensor M ∘ₗ
        ((G.shift 1).koszulTwist 1).rTensor (TensorWords R A) := (rfl)

/-- The unary part on `x ⊗ w` is `d x ⊗ w + τ x ⊗ b w`. -/
@[simp]
theorem unaryBarDifferential_tmul (x : M) (w : TensorWords R A) :
    unaryBarDifferential AA G d (x ⊗ₜ[R] w) =
      d x ⊗ₜ[R] w + (G.shift 1).koszulTwist 1 x ⊗ₜ[R] AA.coaugmentedBarDifferential w := by
  simp [unaryBarDifferential_def]

/-- The unary part is the coderivation generated by `x ⊗ w ↦ ε(w) d x`. -/
theorem unaryBarDifferential_eq_gradedCoderiv :
    unaryBarDifferential AA G d = gradedCoderiv AA G
      ((TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ
          d.rTensor (TensorWords R A)) := by
  have h := Comodule.Hom.cofreeLift_rid_comp_lTensor_counit_comp
    (Comodule.Hom.cofreeMap (C := TensorWords R A) d)
  rw [Comodule.Hom.cofreeMap_toLinearMap] at h
  rw [gradedCoderiv_def, ← comul_eq_deconcatenation, ← Comodule.cofree_coact,
    ← Comodule.Hom.cofreeLift_toLinearMap, h, Comodule.Hom.cofreeMap_toLinearMap,
    unaryBarDifferential_def]

/-- The unary part is a coderivation over the algebra bar differential. -/
theorem isGradedCoderivationOver_unaryBarDifferential :
    Comodule.IsGradedCoderivationOver (barGrading AA G) 1 AA.coaugmentedBarDifferential
      (unaryBarDifferential AA G d) := by
  rw [unaryBarDifferential_eq_gradedCoderiv]
  exact isGradedCoderivationOver_gradedCoderiv _ _

variable {d}

/-- The unary part has degree one when `d` does for the suspended grading. -/
theorem isHomogeneous_unaryBarDifferential
    (hd : LinearMap.IsHomogeneous d (G.shift 1).piece (G.shift 1).piece 1) :
    LinearMap.IsHomogeneous (unaryBarDifferential AA G d) (barGrading AA G).piece
      (barGrading AA G).piece 1 := by
  rw [unaryBarDifferential_eq_gradedCoderiv]
  refine isHomogeneous_gradedCoderiv _ ?_
  have hd' := hd.tensorProduct
    (LinearMap.isHomogeneous_id (R := R) (TensorWords.grading (AA.grading.shift 1)).piece)
  rw [barGrading_def, LinearMap.rTensor_def]
  simpa only [zero_add, add_zero, LinearMap.comp_assoc] using
    (TensorWords.isHomogeneous_rid_comp_lTensor_counit (G.shift 1) (AA.grading.shift 1)).comp hd'

/-- The unary part squares to zero when `d` has degree one and squares to zero, since the Koszul
twist anticommutes with `d` and the algebra bar differential squares to zero. -/
theorem unaryBarDifferential_comp_self
    (hd : LinearMap.IsHomogeneous d (G.shift 1).piece (G.shift 1).piece 1)
    (hdd : d ∘ₗ d = 0) :
    unaryBarDifferential AA G d ∘ₗ unaryBarDifferential AA G d = 0 := by
  refine TensorProduct.ext' fun x w ↦ ?_
  have hdd := LinearMap.congr_fun hdd x
  have hbb := LinearMap.congr_fun AA.coaugmentedBarDifferential_sq w
  have hτd : (G.shift 1).koszulTwist 1 (d x) = -d ((G.shift 1).koszulTwist 1 x) := by
    simpa using hd.koszulTwist_apply 1 x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdd hbb
  simp only [LinearMap.comp_apply, unaryBarDifferential_tmul, map_add, LinearMap.zero_apply,
    hdd, hbb, hτd, InternalGrading.koszulTwist_koszulTwist, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, TensorProduct.neg_tmul]
  abel

end Unary

variable (MM : AInfinityRightModule AA M)

/-- The differential of a right `A∞` module has degree one for the suspended grading. -/
private theorem isHomogeneous_differential_shift :
    LinearMap.IsHomogeneous MM.differential (MM.grading.shift 1).piece
      (MM.grading.shift 1).piece 1 :=
  LinearMap.isHomogeneous_shift_piece_iff.2 MM.isHomogeneous_differential

/-- The **higher part** of the bar differential of a right `A∞` module: the difference between
the bar differential and its unary part.  It applies the module operations with at least one
algebra input to the nonempty prefixes of a word
(`TauCeti.AInfinityRightModule.higherBarDifferential_tmul_of_tprod`). -/
noncomputable def higherBarDifferential : Module.End R (M ⊗[R] TensorWords R A) :=
  MM.barDifferential - unaryBarDifferential AA MM.grading MM.differential

/-- The higher part is the bar differential minus its unary part. -/
theorem higherBarDifferential_def :
    MM.higherBarDifferential =
      MM.barDifferential - unaryBarDifferential AA MM.grading MM.differential := (rfl)

/-- The bar differential is the sum of its unary and higher parts. -/
theorem unaryBarDifferential_add_higherBarDifferential :
    unaryBarDifferential AA MM.grading MM.differential + MM.higherBarDifferential =
      MM.barDifferential :=
  add_sub_cancel _ _

/-- The higher part on the word `x ⊗ a₀ ⊗ ⋯ ⊗ aₙ₋₁`: the sum over the nonempty prefixes of the
word of the Taylor map applied to the module input and the prefix, tensored with the suffix. -/
theorem higherBarDifferential_tmul_of_tprod (n : ℕ) (x : M) (a : Fin n → A) :
    MM.higherBarDifferential (x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a)) =
      ∑ k ∈ Finset.range n,
        MM.taylor (x ⊗ₜ[R] subword R a 0 (k + 1)) ⊗ₜ[R] subword R a (k + 1) (n - (k + 1)) := by
  rw [higherBarDifferential_def, LinearMap.sub_apply, barDifferential_eq,
    gradedCoderiv_tmul_of_tprod, Finset.sum_range_succ', unaryBarDifferential_tmul,
    subword_length_zero R a (Nat.zero_le n), taylor_tmul_one_eq_differential, Nat.sub_zero,
    ← of_tprod_eq_subword]
  abel

/-- The higher part vanishes on the empty algebra word. -/
@[simp]
theorem higherBarDifferential_tmul_one (x : M) :
    MM.higherBarDifferential (x ⊗ₜ[R] (1 : TensorWords R A)) = 0 := by
  have hone : TensorWords.of R A 0 (PiTensorProduct.tprod R (fun i ↦ i.elim0 : Fin 0 → A)) = 1 :=
    by rw [of_tprod_eq_subword, subword_length_zero R _ le_rfl]
  rw [← hone, higherBarDifferential_tmul_of_tprod, Finset.sum_range_zero]

/-- The higher part has degree one. -/
theorem isHomogeneous_higherBarDifferential :
    LinearMap.IsHomogeneous MM.higherBarDifferential (barGrading AA MM.grading).piece
      (barGrading AA MM.grading).piece 1 :=
  MM.isHomogeneous_barDifferential.sub
    (isHomogeneous_unaryBarDifferential AA MM.grading MM.isHomogeneous_differential_shift)

/-- The higher part commutes with the coaction: it is the difference of two coderivations over
the same algebra bar differential. -/
theorem coact_comp_higherBarDifferential :
    Comodule.coact (R := R) (C := TensorWords R A) (M := M ⊗[R] TensorWords R A) ∘ₗ
        MM.higherBarDifferential =
      MM.higherBarDifferential.rTensor (TensorWords R A) ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R A) (M := M ⊗[R] TensorWords R A) := by
  refine LinearMap.ext fun z ↦ ?_
  simp only [higherBarDifferential_def, LinearMap.comp_apply, LinearMap.sub_apply, map_sub,
    MM.isGradedCoderivation_barDifferential.coact_apply z,
    (isGradedCoderivationOver_unaryBarDifferential AA MM.grading MM.differential).coact_apply z,
    LinearMap.rTensor_sub]
  abel

/-- On a pure word of length `n`, `δ (k ⊗ 1)` produces words of length less than `n`, so by
strong induction its `(n + 1)`-st power kills the word. -/
private theorem pow_succ_higherBarDifferential_comp_rTensor_tmul_of_tprod (k : Module.End R M)
    (n : ℕ) (x : M) (a : Fin n → A) :
    ((MM.higherBarDifferential ∘ₗ k.rTensor (TensorWords R A)) ^ (n + 1))
      (x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a)) = 0 := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    rw [pow_succ, Module.End.mul_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      higherBarDifferential_tmul_of_tprod, map_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hj : j < n := Finset.mem_range.1 hj
    have hle : j + 1 + (n - (j + 1)) ≤ n := by omega
    rw [subword_eq_of_tprod R a hle]
    exact Module.End.pow_map_zero_of_le (k := n - (j + 1) + 1) (by omega)
      (ih (n - (j + 1)) (by omega) _ fun i ↦ a ⟨j + 1 + i.1, by omega⟩)

/-- **Local nilpotence.**  Followed by any map `k ⊗ 1` acting on the module input only, the higher
part is locally nilpotent, since it strictly lowers the length of the algebra word. -/
theorem exists_pow_higherBarDifferential_comp_rTensor_apply_eq_zero (k : Module.End R M)
    (z : M ⊗[R] TensorWords R A) :
    ∃ n, ((MM.higherBarDifferential ∘ₗ k.rTensor (TensorWords R A)) ^ n) z = 0 := by
  set f : Module.End R (M ⊗[R] TensorWords R A) :=
    MM.higherBarDifferential ∘ₗ k.rTensor (TensorWords R A)
  -- The vectors killed by a power of `f` form the submodule `P`.
  let P := Module.End.maxGenEigenspace f 0
  have hmem (z) : z ∈ P ↔ ∃ n, (f ^ n) z = 0 := by
    simp only [P, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero]
  have hP : ∀ z, z ∈ P := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => exact P.add_mem hz hz'
    | tmul x w =>
      have h : P.mkQ ∘ₗ TensorProduct.mk R M (TensorWords R A) x = 0 :=
        TensorWords.linearMap_ext R A fun n a ↦ by
          rw [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.zero_apply,
            Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmem]
          exact ⟨n + 1, MM.pow_succ_higherBarDifferential_comp_rTensor_tmul_of_tprod k n x a⟩
      have hw := LinearMap.congr_fun h w
      rwa [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.zero_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw
  exact (hmem z).1 (hP z)

/-- The unit required by the perturbation lemma: `1 + δ (k ⊗ 1)` is invertible. -/
theorem isUnit_one_add_higherBarDifferential_mul_rTensor (k : Module.End R M) :
    IsUnit (1 + MM.higherBarDifferential * k.rTensor (TensorWords R A)) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _
    (MM.exists_pow_higherBarDifferential_comp_rTensor_apply_eq_zero k)

/-- A map `f ⊗ 1` acting on the module input only commutes with the cofree coactions. -/
private theorem coact_comp_rTensor {P : Type*} [AddCommGroup P] [Module R P] (f : P →ₗ[R] N) :
    Comodule.coact (R := R) (C := TensorWords R A) (M := N ⊗[R] TensorWords R A) ∘ₗ
        f.rTensor (TensorWords R A) =
      (f.rTensor (TensorWords R A)).rTensor (TensorWords R A) ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R A) (M := P ⊗[R] TensorWords R A) :=
  (Comodule.Hom.cofreeMap (C := TensorWords R A) f).map_coact_eq.symm

/-! ### The bar contraction and the perturbation -/

section Transfer

variable {GN : InternalGrading R N} {dN : Module.End R N}
  (c : LinearSpecialContraction MM.differential dN)
  (hh : LinearMap.IsHomogeneous c.homotopy MM.grading.piece MM.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GN.piece MM.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj MM.grading.piece GN.piece 0)

/-- The **bar contraction**: a special contraction of `(M, m₁)` onto `(N, d_N)` induces the
special contraction `(i ⊗ 1, p ⊗ 1, h ⊗ 1)` of the bar comodules `sM ⊗ Tᶜ(sA)` onto
`sN ⊗ Tᶜ(sA)` for the unary parts of the bar differentials. -/
noncomputable def barContraction :
    LinearSpecialContraction (unaryBarDifferential AA MM.grading MM.differential)
      (unaryBarDifferential AA GN dN) :=
  c.rTensor (LinearMap.isHomogeneous_shift_piece_iff.2 hh)
    (LinearMap.isHomogeneous_shift_piece_iff.2 hincl)
    (LinearMap.isHomogeneous_shift_piece_iff.2 hproj) AA.coaugmentedBarDifferential

/-- The inclusion of the bar contraction is `i ⊗ 1`. -/
@[simp]
theorem barContraction_incl :
    (MM.barContraction c hh hincl hproj).incl = c.incl.rTensor (TensorWords R A) :=
  LinearSpecialContraction.rTensor_incl ..

/-- The projection of the bar contraction is `p ⊗ 1`. -/
@[simp]
theorem barContraction_proj :
    (MM.barContraction c hh hincl hproj).proj = c.proj.rTensor (TensorWords R A) :=
  LinearSpecialContraction.rTensor_proj ..

/-- The homotopy of the bar contraction is `h ⊗ 1`. -/
@[simp]
theorem barContraction_homotopy :
    (MM.barContraction c hh hincl hproj).homotopy = c.homotopy.rTensor (TensorWords R A) :=
  LinearSpecialContraction.rTensor_homotopy ..

/-- The higher part is a perturbation of the unary part: `(D₀ + δ)² = D₀²`, since `D₀ + δ` is the
bar differential and both sides vanish. -/
theorem unaryBarDifferential_add_higherBarDifferential_comp_self :
    (unaryBarDifferential AA MM.grading MM.differential + MM.higherBarDifferential) ∘ₗ
        (unaryBarDifferential AA MM.grading MM.differential + MM.higherBarDifferential) =
      unaryBarDifferential AA MM.grading MM.differential ∘ₗ
        unaryBarDifferential AA MM.grading MM.differential := by
  rw [unaryBarDifferential_add_higherBarDifferential, barDifferential_sq,
    unaryBarDifferential_comp_self AA MM.grading MM.isHomogeneous_differential_shift
      MM.differential_comp_self_eq_zero]

/-- The unit hypothesis of the perturbation lemma for the bar contraction. -/
theorem isUnit_one_add_higherBarDifferential_mul_barContraction_homotopy :
    IsUnit (1 + MM.higherBarDifferential * (MM.barContraction c hh hincl hproj).homotopy) := by
  rw [barContraction_homotopy]
  exact MM.isUnit_one_add_higherBarDifferential_mul_rTensor c.homotopy

/-- The perturbation operator `X = (1 + δ (h ⊗ 1))⁻¹ δ` commutes with the coaction, since `δ` and
`h ⊗ 1` do. -/
theorem coact_comp_perturbationSeries :
    Comodule.coact (R := R) (C := TensorWords R A) (M := M ⊗[R] TensorWords R A) ∘ₗ
        (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential =
      ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential).rTensor
          (TensorWords R A) ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R A) (M := M ⊗[R] TensorWords R A) := by
  -- Package `δ`, and hence `1 + δ (h ⊗ 1)`, its inverse and `X`, as comodule morphisms.
  let δ : Comodule.Hom R (TensorWords R A) (M ⊗[R] TensorWords R A) (M ⊗[R] TensorWords R A) :=
    ⟨MM.higherBarDifferential, MM.coact_comp_higherBarDifferential.symm⟩
  let U := Comodule.Hom.id R (TensorWords R A) (M ⊗[R] TensorWords R A) +
    δ.comp (Comodule.Hom.cofreeMap c.homotopy)
  have hX := ((Comodule.Hom.ringInverse U).comp δ).map_coact_eq
  rw [Comodule.Hom.comp_toLinearMap, Comodule.Hom.ringInverse_toLinearMap] at hX
  rw [LinearSpecialContraction.perturbationSeries_def, barContraction_homotopy]
  exact hX.symm

/-- The perturbation operator has degree one. -/
theorem isHomogeneous_perturbationSeries :
    LinearMap.IsHomogeneous
      ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential)
      (barGrading AA MM.grading).piece (barGrading AA MM.grading).piece 1 := by
  have hK : LinearMap.IsHomogeneous (c.homotopy.rTensor (TensorWords R A))
      (barGrading AA MM.grading).piece (barGrading AA MM.grading).piece (-1) :=
    isHomogeneous_rTensor hh
  have hδK : LinearMap.IsHomogeneous
      (MM.higherBarDifferential * c.homotopy.rTensor (TensorWords R A))
      (barGrading AA MM.grading).piece (barGrading AA MM.grading).piece 0 := by
    rw [Module.End.mul_eq_comp]
    simpa only [neg_add_cancel] using MM.isHomogeneous_higherBarDifferential.comp hK
  have hinv := hδK.ringInverse_one_add fun z ↦ by
    rw [Module.End.mul_eq_comp]
    exact MM.exists_pow_higherBarDifferential_comp_rTensor_apply_eq_zero c.homotopy z
  rw [LinearSpecialContraction.perturbationSeries_def, barContraction_homotopy,
    Module.End.mul_eq_comp]
  simpa only [add_zero] using hinv.comp MM.isHomogeneous_higherBarDifferential

/-- The perturbation operator vanishes on the empty algebra word, since the higher part does. -/
@[simp]
theorem perturbationSeries_tmul_one (x : M) :
    (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential
      (x ⊗ₜ[R] (1 : TensorWords R A)) = 0 := by
  rw [LinearSpecialContraction.perturbationSeries_def, Module.End.mul_apply,
    higherBarDifferential_tmul_one, map_zero]

/-! ### The transferred module -/

/-- The **transferred bar differential**: the perturbed differential
`D' = D₀' + (p ⊗ 1) X (i ⊗ 1)` of `sN ⊗ Tᶜ(sA)`, obtained from the bar contraction by perturbing
along the higher part of the module bar differential. -/
noncomputable def transferBarDifferential : Module.End R (N ⊗[R] TensorWords R A) :=
  (MM.barContraction c hh hincl hproj).perturbedDifferential MM.higherBarDifferential

/-- The transferred bar differential is `D₀' + (p ⊗ 1) X (i ⊗ 1)`. -/
theorem transferBarDifferential_def :
    MM.transferBarDifferential c hh hincl hproj =
      unaryBarDifferential AA GN dN + c.proj.rTensor (TensorWords R A) ∘ₗ
        (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
          c.incl.rTensor (TensorWords R A) := by
  rw [transferBarDifferential, LinearSpecialContraction.perturbedDifferential_def,
    barContraction_incl, barContraction_proj]

/-- The **perturbed bar contraction**: the basic perturbation lemma applied to the bar contraction
and the higher part of the module bar differential.  It is a special contraction of the bar
comodule of `M`, with its bar differential `D₀ + δ`, onto `sN ⊗ Tᶜ(sA)` with the transferred bar
differential. -/
noncomputable def transferContraction :
    LinearSpecialContraction
      (unaryBarDifferential AA MM.grading MM.differential + MM.higherBarDifferential)
      (MM.transferBarDifferential c hh hincl hproj) :=
  (MM.barContraction c hh hincl hproj).perturb MM.higherBarDifferential
    MM.unaryBarDifferential_add_higherBarDifferential_comp_self
    (MM.isUnit_one_add_higherBarDifferential_mul_barContraction_homotopy c hh hincl hproj)

/-- The inclusion of the perturbed bar contraction is `i' = i ⊗ 1 - (h ⊗ 1) X (i ⊗ 1)`. -/
theorem transferContraction_incl :
    (MM.transferContraction c hh hincl hproj).incl =
      c.incl.rTensor (TensorWords R A) - c.homotopy.rTensor (TensorWords R A) ∘ₗ
        (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
          c.incl.rTensor (TensorWords R A) := by
  rw [transferContraction, LinearSpecialContraction.perturb_incl, barContraction_incl,
    barContraction_homotopy]

/-- The projection of the perturbed bar contraction is `p' = p ⊗ 1 - (p ⊗ 1) X (h ⊗ 1)`. -/
theorem transferContraction_proj :
    (MM.transferContraction c hh hincl hproj).proj =
      c.proj.rTensor (TensorWords R A) - c.proj.rTensor (TensorWords R A) ∘ₗ
        (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
          c.homotopy.rTensor (TensorWords R A) := by
  rw [transferContraction, LinearSpecialContraction.perturb_proj, barContraction_proj,
    barContraction_homotopy]

/-- The perturbed inclusion commutes with the coactions. -/
theorem coact_comp_transferContraction_incl :
    Comodule.coact (R := R) (C := TensorWords R A) (M := M ⊗[R] TensorWords R A) ∘ₗ
        (MM.transferContraction c hh hincl hproj).incl =
      (MM.transferContraction c hh hincl hproj).incl.rTensor (TensorWords R A) ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R A) (M := N ⊗[R] TensorWords R A) := by
  refine LinearMap.ext fun z ↦ ?_
  have hi := LinearMap.congr_fun (coact_comp_rTensor (A := A) c.incl)
  have hh' := LinearMap.congr_fun (coact_comp_rTensor (A := A) c.homotopy)
  have hX := LinearMap.congr_fun (MM.coact_comp_perturbationSeries c hh hincl hproj)
  simp only [LinearMap.comp_apply] at hi hh' hX
  simp only [transferContraction_incl, LinearMap.comp_apply, LinearMap.sub_apply, map_sub,
    LinearMap.rTensor_sub, hi, hh', hX, LinearMap.rTensor_comp_apply]

/-- The perturbed projection commutes with the coactions. -/
theorem coact_comp_transferContraction_proj :
    Comodule.coact (R := R) (C := TensorWords R A) (M := N ⊗[R] TensorWords R A) ∘ₗ
        (MM.transferContraction c hh hincl hproj).proj =
      (MM.transferContraction c hh hincl hproj).proj.rTensor (TensorWords R A) ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R A) (M := M ⊗[R] TensorWords R A) := by
  refine LinearMap.ext fun z ↦ ?_
  have hp := LinearMap.congr_fun (coact_comp_rTensor (A := A) c.proj)
  have hh' := LinearMap.congr_fun (coact_comp_rTensor (A := A) c.homotopy)
  have hX := LinearMap.congr_fun (MM.coact_comp_perturbationSeries c hh hincl hproj)
  simp only [LinearMap.comp_apply] at hp hh' hX
  simp only [transferContraction_proj, LinearMap.comp_apply, LinearMap.sub_apply, map_sub,
    LinearMap.rTensor_sub, hp, hh', hX, LinearMap.rTensor_comp_apply]

/-- The transferred bar differential is a coderivation over the algebra bar differential: it is
the unary part for `d_N` plus the comodule morphism `(p ⊗ 1) X (i ⊗ 1)`. -/
theorem isGradedCoderivationOver_transferBarDifferential :
    Comodule.IsGradedCoderivationOver (barGrading AA GN) 1 AA.coaugmentedBarDifferential
      (MM.transferBarDifferential c hh hincl hproj) := by
  have hp := LinearMap.congr_fun (coact_comp_rTensor (A := A) c.proj)
  have hi := LinearMap.congr_fun (coact_comp_rTensor (A := A) c.incl)
  have hX := LinearMap.congr_fun (MM.coact_comp_perturbationSeries c hh hincl hproj)
  have hD := (isGradedCoderivationOver_unaryBarDifferential AA GN dN).coact_apply
  simp only [LinearMap.comp_apply] at hp hi hX
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
    (MM.isUnit_one_add_higherBarDifferential_mul_barContraction_homotopy c hh hincl hproj)
    (unaryBarDifferential_comp_self AA MM.grading MM.isHomogeneous_differential_shift
      MM.differential_comp_self_eq_zero)

include hincl hproj in
/-- The differential of the retract has degree one for the suspended grading. -/
private theorem isHomogeneous_dN_shift :
    LinearMap.IsHomogeneous dN (GN.shift 1).piece (GN.shift 1).piece 1 :=
  LinearMap.isHomogeneous_shift_piece_iff.2 <| c.isHomogeneous_dN MM.isHomogeneous_differential
    hincl hproj

/-- The transferred bar differential has degree one. -/
theorem isHomogeneous_transferBarDifferential :
    LinearMap.IsHomogeneous (MM.transferBarDifferential c hh hincl hproj)
      (barGrading AA GN).piece (barGrading AA GN).piece 1 := by
  rw [transferBarDifferential_def]
  have hpXi := (isHomogeneous_rTensor hproj).comp
    ((MM.isHomogeneous_perturbationSeries c hh hincl hproj).comp (isHomogeneous_rTensor hincl))
  simpa only [zero_add, add_zero] using
    (isHomogeneous_unaryBarDifferential AA GN (MM.isHomogeneous_dN_shift c hincl hproj)).add hpXi

/-- The **transferred right `A∞` module** on the retract `N` of a special contraction of
`(M, m₁)`: its bar differential is the transferred bar differential. -/
noncomputable def transfer : AInfinityRightModule AA N :=
  ofBarDifferential GN (MM.transferBarDifferential c hh hincl hproj)
    (MM.isHomogeneous_transferBarDifferential c hh hincl hproj)
    (MM.isGradedCoderivationOver_transferBarDifferential c hh hincl hproj)
    (by rw [LinearMap.comp_assoc, LinearMap.comp_assoc, transferBarDifferential_comp_self,
      LinearMap.comp_zero, LinearMap.comp_zero])

/-- The transferred module lives on the grading of the retract. -/
@[simp]
theorem transfer_grading : (MM.transfer c hh hincl hproj).grading = GN :=
  ofBarDifferential_grading ..

/-- The bar differential of the transferred module is the transferred bar differential. -/
@[simp]
theorem barDifferential_transfer :
    (MM.transfer c hh hincl hproj).barDifferential = MM.transferBarDifferential c hh hincl hproj :=
  ofBarDifferential_barDifferential ..

/-- The unary operation of the transferred module is the differential of the retract. -/
@[simp]
theorem differential_transfer : (MM.transfer c hh hincl hproj).differential = dN := by
  ext y
  rw [← taylor_tmul_one_eq_differential, taylor_apply, barDifferential_transfer,
    transferBarDifferential_def]
  simp [AA.coaugmentedBarDifferential_one, TensorWords.counit_eq_counit, TensorWords.counit_one]

/-! ### The extending and projecting morphisms -/

/-- The perturbed inclusion has degree zero. -/
theorem isHomogeneous_transferContraction_incl :
    LinearMap.IsHomogeneous (MM.transferContraction c hh hincl hproj).incl
      (barGrading AA GN).piece (barGrading AA MM.grading).piece 0 := by
  rw [transferContraction_incl]
  have hhXi := (isHomogeneous_rTensor hh).comp
    ((MM.isHomogeneous_perturbationSeries c hh hincl hproj).comp (isHomogeneous_rTensor hincl))
  simpa only [zero_add, add_neg_cancel] using (isHomogeneous_rTensor hincl).sub hhXi

/-- The perturbed projection has degree zero. -/
theorem isHomogeneous_transferContraction_proj :
    LinearMap.IsHomogeneous (MM.transferContraction c hh hincl hproj).proj
      (barGrading AA MM.grading).piece (barGrading AA GN).piece 0 := by
  rw [transferContraction_proj]
  have hpXh := (isHomogeneous_rTensor hproj).comp
    ((MM.isHomogeneous_perturbationSeries c hh hincl hproj).comp (isHomogeneous_rTensor hh))
  simpa only [zero_add, neg_add_cancel] using (isHomogeneous_rTensor hproj).sub hpXh

/-- The **extending morphism** of right `A∞` modules from the transferred module to `M`: its bar
map is the perturbed inclusion `i' = i ⊗ 1 - (h ⊗ 1) X (i ⊗ 1)`. -/
noncomputable def transferInclusion :
    AInfinityRightModuleHom (MM.transfer c hh hincl hproj) MM where
  barHom := ⟨(MM.transferContraction c hh hincl hproj).incl,
    (MM.coact_comp_transferContraction_incl c hh hincl hproj).symm⟩
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

/-- The **projecting morphism** of right `A∞` modules from `M` to the transferred module: its bar
map is the perturbed projection `p' = p ⊗ 1 - (p ⊗ 1) X (h ⊗ 1)`. -/
noncomputable def transferProjection :
    AInfinityRightModuleHom MM (MM.transfer c hh hincl hproj) where
  barHom := ⟨(MM.transferContraction c hh hincl hproj).proj,
    (MM.coact_comp_transferContraction_proj c hh hincl hproj).symm⟩
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
  simp [AInfinityRightModuleHom.taylor_def, transferContraction_incl,
    TensorWords.counit_eq_counit, TensorWords.counit_one]

/-- The linear part of the projecting morphism is the projection of the contraction. -/
@[simp]
theorem linearPart_transferProjection :
    (MM.transferProjection c hh hincl hproj).linearPart = c.proj := by
  ext x
  simp [AInfinityRightModuleHom.taylor_def, transferContraction_proj,
    TensorWords.counit_eq_counit, TensorWords.counit_one]

/-- The projecting morphism is a left inverse of the extending morphism. -/
@[simp]
theorem transferProjection_comp_transferInclusion :
    (MM.transferProjection c hh hincl hproj).comp (MM.transferInclusion c hh hincl hproj) =
      AInfinityRightModuleHom.id _ :=
  AInfinityRightModuleHom.barMap_injective <| by
    rw [AInfinityRightModuleHom.barMap_comp, barMap_transferProjection, barMap_transferInclusion,
      AInfinityRightModuleHom.barMap_id]
    exact (MM.transferContraction c hh hincl hproj).proj_comp_incl

/-- The extending morphism is a quasi-isomorphism: its linear part is the inclusion of a
contraction. -/
theorem isQuasiIso_transferInclusion : (MM.transferInclusion c hh hincl hproj).IsQuasiIso := by
  rw [AInfinityRightModuleHom.isQuasiIso_iff, linearPart_transferInclusion]
  refine ⟨fun x _ hx ↦ ?_, fun y hy ↦ ⟨c.proj y, ?_, ?_⟩⟩
  · obtain ⟨y, hy⟩ := (MM.mem_boundaries).1 hx
    rw [mem_boundaries, differential_transfer]
    exact ⟨c.proj y, by rw [← c.proj_dM_apply, hy, c.proj_incl_apply]⟩
  · rw [mem_cycles, differential_transfer, ← c.proj_dM_apply, (MM.mem_cycles).1 hy, map_zero]
  · rw [c.incl_proj_apply, (MM.mem_cycles).1 hy, map_zero, sub_zero, sub_sub_cancel]
    exact (MM.mem_boundaries).2 ⟨c.homotopy y, rfl⟩

/-- The projecting morphism is a quasi-isomorphism. -/
theorem isQuasiIso_transferProjection : (MM.transferProjection c hh hincl hproj).IsQuasiIso :=
  (MM.isQuasiIso_transferInclusion c hh hincl hproj).of_precomp <| by
    rw [transferProjection_comp_transferInclusion]
    exact AInfinityRightModuleHom.isQuasiIso_id _

end Transfer

end AInfinityRightModule

end TauCeti
