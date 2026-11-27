/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.Exponential
public import TauCeti.Analysis.CStarAlgebra.Projection.Equivalence
public import TauCeti.Topology.Algebra.Star.StarProjection
import TauCeti.Analysis.CStarAlgebra.Unitary.Connected
import TauCeti.Data.Matrix.Block

/-!
# Stabilization, unitization descent, and paths for projection equivalence

Stabilization and unitization results for Murray–von Neumann equivalence
(`TauCeti.Analysis.CStarAlgebra.Projection.Equivalence`) on `CStarMatrix` over a (possibly
non-unital) C⋆-algebra `A`: rectangular unitization descent, the self-adjoint unitary
`stabilizedConjUnitary` sending `blockSum p 0` to `blockSum 0 q`, the exponential unitary path
`stabilizedConjUnitaryPath` (built from Mathlib's `selfAdjoint.expUnitaryPathToOne`) and
conjugation formula `expUnitary_conj_blockSum_eq_stabilizedProjRot` over a star-ordered unital
C⋆-algebra `A`, the unit-free projection path `stabilizedProjPath`, and stabilized comparison with
`TauCeti.IsUnitarilyEquivalent` and `TauCeti.IsHomotopicProjection`.

## Main definitions and statements

* `IsStarProjection.murrayVonNeumannEquiv_of_conj_unitization`,
  `IsStarProjection.murrayVonNeumannEquiv_of_unitary_conj_unitization`.
* `CStarMatrix.IsPartialIsometry.stabilizedConjUnitary`, `stabilizedNegProj`, `stabilizedProjRot`,
  `stabilizedConjUnitaryPath`, `stabilizedConjUnitaryPath_conj`,
  `expUnitary_conj_blockSum_eq_stabilizedProjRot`, `stabilizedProjPath`.
* `CStarMatrix.MurrayVonNeumannEquiv.exists_isSelfAdjoint_unitary_conj_blockSum_eq`,
  `CStarMatrix.MurrayVonNeumannEquiv.isUnitarilyEquivalent_blockSum`,
  `CStarMatrix.MurrayVonNeumannEquiv.exists_joined_one_unitary_conj_blockSum_eq`,
  `CStarMatrix.MurrayVonNeumannEquiv.joined_blockSum`,
  `CStarMatrix.MurrayVonNeumannEquiv.isHomotopicProjection_blockSum`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6 and §5.1.
-/

public section

noncomputable section

open scoped Matrix ComplexOrder

namespace CStarMatrix
variable {k l m n o R A : Type*}

section
variable [Fintype m] [Fintype n] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
/-- Rectangular unitization descent: if `u : CStarMatrix n m (Unitization R A)` satisfies
`uᴴ * u * p.map ι = p.map ι` and `u * p.map ι * uᴴ = q.map ι` for projections `p, q` over `A`,
then `p ∼ q`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_of_conj_unitization
    [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix m m A} (hp : IsStarProjection p)
    (R : Type*) [CommSemiring R] [StarRing R] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [StarModule R A] {q : CStarMatrix n n A}
    (u : CStarMatrix n m (Unitization R A))
    (hu_init : u.conjTranspose * u * p.map (Unitization.inrNonUnitalStarAlgHom R A) =
      p.map (Unitization.inrNonUnitalStarAlgHom R A))
    (hu_conj : u * p.map (Unitization.inrNonUnitalStarAlgHom R A) * u.conjTranspose =
      q.map (Unitization.inrNonUnitalStarAlgHom R A)) : p.MurrayVonNeumannEquiv q := by
  let ι := Unitization.inrNonUnitalStarAlgHom R A
  let w : CStarMatrix n m (Unitization R A) := u * p.map ι
  let v : CStarMatrix n m A := ofMatrix fun i j => (w i j).snd
  have hv_map : v.map ι = w := CStarMatrix.ext fun i j => Unitization.ext (by
    simp only [map_apply, ι, Unitization.inrNonUnitalStarAlgHom_apply, Unitization.fst_inr]
    dsimp only [w]; rw [mul_apply, ← Unitization.fstHom_apply, map_sum]
    exact (Finset.sum_eq_zero fun k _ => by simp [ι, Unitization.fst_mul]).symm) rfl
  have hpι : IsStarProjection (p.map ι) := by rw [← mapₙₐ_eq_map]; exact hp.map (mapₙₐ ι)
  have hv : v.IsPartialIsometry := by
    rw [isPartialIsometry_iff]
    exact CStarMatrix.map_injective (f := ⇑ι) Unitization.inr_injective <| by
      simpa only [map_mul, map_conjTranspose, hv_map, ι, w] using
        (IsPartialIsometry.mul_of_conjTranspose_mul_self_mul_eq_of_isStarProjection
          hu_init hpι).mul_conjTranspose_mul_self
  have hvp : v.conjTranspose * v = p :=
    CStarMatrix.map_injective (f := ⇑ι) Unitization.inr_injective <| by
      simpa only [map_mul, map_conjTranspose, hv_map, ι, w] using
        hpι.conjTranspose_mul_self_mul_of_conjTranspose_mul_self_mul_eq hu_init
  have hvq : v * v.conjTranspose = q :=
    CStarMatrix.map_injective (f := ⇑ι) Unitization.inr_injective <| by
      simpa only [map_mul, map_conjTranspose, hv_map, ι, w] using
        (self_mul_conjTranspose_mul_of_isStarProjection u hpι).trans hu_conj
  exact hvp ▸ hvq ▸ hv.murrayVonNeumannEquiv
/-- Unitary conjugacy over `Unitization R A` between projections from `A` gives `p ∼ q`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_of_unitary_conj_unitization
    [DecidableEq n] [NonUnitalSemiring A] [StarRing A] {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (R : Type*) [CommSemiring R] [StarRing R] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
    (u : unitary (CStarMatrix n n (Unitization R A)))
    (hu : (u : CStarMatrix n n (Unitization R A)) * p.map (Unitization.inrNonUnitalStarAlgHom R A) *
        star (u : CStarMatrix n n (Unitization R A)) =
      q.map (Unitization.inrNonUnitalStarAlgHom R A)) : p.MurrayVonNeumannEquiv q :=
  hp.murrayVonNeumannEquiv_of_conj_unitization R (u : CStarMatrix n n (Unitization R A))
    (by rw [← star_eq_conjTranspose, Unitary.coe_star_mul_self, CStarMatrix.one_mul])
    (by rwa [← star_eq_conjTranspose])
end

namespace IsPartialIsometry
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
  {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
  (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q)
include hv hp hq
omit [DecidableEq m] [DecidableEq n] in
private theorem stabilizedConjUnitary_matrix_witness :
    (ofMatrix.symm v)ᴴ * ofMatrix.symm v = ofMatrix.symm p ∧
      ofMatrix.symm v * (ofMatrix.symm v)ᴴ = ofMatrix.symm q ∧
      ofMatrix.symm p * (ofMatrix.symm v)ᴴ = (ofMatrix.symm v)ᴴ ∧
      ofMatrix.symm v * ofMatrix.symm p = ofMatrix.symm v :=
  ⟨by simpa using congrArg ofMatrix.symm hp, by simpa using congrArg ofMatrix.symm hq,
   by simpa using congrArg ofMatrix.symm (hv.mul_conjTranspose_eq_of_conjTranspose_mul_self_eq hp),
   by simpa using congrArg ofMatrix.symm (hv.mul_eq_self_of_conjTranspose_mul_self_eq hp)⟩
private theorem isSelfAdjoint_fromBlocks_one_sub :
    IsSelfAdjoint (fromBlocks (1 - p) v.conjTranspose v (1 - q)) := by
  simp [isSelfAdjoint_iff, (hp ▸ hv.isStarProjection_conjTranspose_mul_self).isSelfAdjoint.star_eq,
    (hq ▸ hv.isStarProjection_mul_conjTranspose_self).isSelfAdjoint.star_eq]
/-- Self-adjoint unitary `fromBlocks (1 - p) vᴴ v (1 - q)` sending `p ⊕ 0` to `0 ⊕ q`. -/
def stabilizedConjUnitary : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  ⟨fromBlocks (1 - p) v.conjTranspose v (1 - q), by
    rw [Unitary.mem_iff, (hv.isSelfAdjoint_fromBlocks_one_sub hp hq).star_eq, and_self]
    obtain ⟨hp', hq', h1', h2'⟩ := hv.stabilizedConjUnitary_matrix_witness hp hq
    exact ofMatrix.symm.injective <| by
      simpa only [ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_sub, ofMatrix_symm_one,
        ofMatrix_symm_conjTranspose] using
        Matrix.fromBlocks_one_sub_mul_self_of_mul_eq hp' hq' h1' h2'⟩
@[simp] theorem coe_stabilizedConjUnitary : ((hv.stabilizedConjUnitary hp hq : unitary _) :
    CStarMatrix (m ⊕ n) (m ⊕ n) A) = fromBlocks (1 - p) v.conjTranspose v (1 - q) := (rfl)
/-- The stabilized conjugating unitary `stabilizedConjUnitary` is self-adjoint. -/
theorem isSelfAdjoint_stabilizedConjUnitary :
    IsSelfAdjoint ((hv.stabilizedConjUnitary hp hq : unitary _) : CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  hv.isSelfAdjoint_fromBlocks_one_sub hp hq
/-- `stabilizedConjUnitary` conjugates `blockSum p 0` to `blockSum 0 q`. -/
theorem stabilizedConjUnitary_conj :
    (hv.stabilizedConjUnitary hp hq : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
      star (hv.stabilizedConjUnitary hp hq : CStarMatrix (m ⊕ n) (m ⊕ n) A) = blockSum 0 q := by
  rw [(hv.isSelfAdjoint_stabilizedConjUnitary hp hq).star_eq, coe_stabilizedConjUnitary]
  obtain ⟨hp', hq', _, hvp'⟩ := hv.stabilizedConjUnitary_matrix_witness hp hq
  exact ofMatrix.symm.injective <| by
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_blockSum,
      ofMatrix_symm_sub, ofMatrix_symm_one, ofMatrix_symm_zero, ofMatrix_symm_conjTranspose] using
      Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq hp' hq' hvp'
end IsPartialIsometry

section
variable (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A)
/-- Unit-free `(2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q`, formed using only
`[Neg A] [Star A] [SMul ℝ A]`. When `v` is a partial isometry with initial projection
`p = v.conjTranspose * v` and final projection `q = v * v.conjTranspose` over a unital star ring
with real scalar action, this equals `(2⁻¹ : ℝ) • (1 - w)` for
`w = hv.stabilizedConjUnitary hp hq`; over a non-unital star ring with compatible real module
hypotheses (`Module ℝ A`, `IsScalarTower ℝ A A`, `SMulCommClass ℝ A A`, `StarModule ℝ A`), it is
a star projection (`isStarProjection_stabilizedNegProj`). -/
def stabilizedNegProj [Neg A] [Star A] [SMul ℝ A] : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q
theorem stabilizedNegProj_def [Neg A] [Star A] [SMul ℝ A] :
    stabilizedNegProj v p q = (2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q := (rfl)
/-- Unit-free rotation curve
`fromBlocks ((c ^ 2) • p) ((I * s * c) • vᴴ) ((-I * s * c) • v) ((s ^ 2) • q)` with
`c = cos (π * t / 2)` and `s = sin (π * t / 2)`. Under
`[Zero A] [Star A] [MulActionWithZero ℂ A]`, it starts at `blockSum p 0`
(`stabilizedProjRot_zero`) and ends at `blockSum 0 q` (`stabilizedProjRot_one`). -/
def stabilizedProjRot [Star A] [SMul ℂ A] (t : ℝ) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  let c : ℂ := ↑(Real.cos (Real.pi * t / 2)); let s : ℂ := ↑(Real.sin (Real.pi * t / 2))
  fromBlocks ((c ^ 2) • p) ((Complex.I * s * c) • v.conjTranspose)
    ((-Complex.I * s * c) • v) ((s ^ 2) • q)
theorem stabilizedProjRot_def [Star A] [SMul ℂ A] (t : ℝ) : stabilizedProjRot v p q t =
    fromBlocks (((Real.cos (Real.pi * t / 2) : ℂ) ^ 2) • p)
      ((Complex.I * ↑(Real.sin (Real.pi * t / 2)) * ↑(Real.cos (Real.pi * t / 2))) •
        v.conjTranspose)
      ((-Complex.I * ↑(Real.sin (Real.pi * t / 2)) * ↑(Real.cos (Real.pi * t / 2))) • v)
      (((Real.sin (Real.pi * t / 2) : ℂ) ^ 2) • q) := (rfl)
private def stabilizedProjRotRows [SMul ℂ A] (t : ℝ) : CStarMatrix (m ⊕ n) m A :=
  fromRows ((Real.cos (Real.pi * t / 2) : ℂ) • p) ((-Complex.I * ↑(Real.sin (Real.pi * t / 2))) • v)
@[simp] theorem stabilizedProjRot_zero [Zero A] [Star A] [MulActionWithZero ℂ A] :
    stabilizedProjRot v p q 0 = blockSum p 0 := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [stabilizedProjRot]
@[simp] theorem stabilizedProjRot_one [Zero A] [Star A] [MulActionWithZero ℂ A] :
    stabilizedProjRot v p q 1 = blockSum 0 q := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [stabilizedProjRot]
/-- Midpoint value of `stabilizedProjRot v p q` at `t = 1 / 2`. -/
theorem stabilizedProjRot_half [Star A] [SMul ℂ A] : stabilizedProjRot v p q (1 / 2) =
    fromBlocks ((2⁻¹ : ℂ) • p) ((Complex.I / 2) • v.conjTranspose)
      ((-Complex.I / 2) • v) ((2⁻¹ : ℂ) • q) := by
  have hθ : Real.pi * (1 / 2) / 2 = Real.pi / 4 := by ring
  have hc2 : (Real.cos (Real.pi / 4) : ℂ) ^ 2 = 2⁻¹ := by
    rw [Real.cos_pi_div_four, ← Complex.ofReal_pow, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [stabilizedProjRot_def, hθ]
  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [hc2]
  · simp only [Real.sin_pi_div_four, ← Real.cos_pi_div_four, mul_assoc, ← sq, hc2, ← div_eq_mul_inv]
  · simp only [Real.sin_pi_div_four, ← Real.cos_pi_div_four, mul_assoc, ← sq, hc2, ← div_eq_mul_inv]
  · rw [Real.sin_pi_div_four, ← Real.cos_pi_div_four, hc2]
/-- `stabilizedProjRot v p q` is continuous on `ℝ` for any (possibly non-unital) C⋆-algebra `A`. -/
@[fun_prop] theorem continuous_stabilizedProjRot [NonUnitalCStarAlgebra A] :
    Continuous (stabilizedProjRot v p q) := by unfold stabilizedProjRot; fun_prop
end

namespace IsPartialIsometry
variable [Fintype m] [Fintype n] {v : CStarMatrix n m A} {p : CStarMatrix m m A}
  {q : CStarMatrix n n A}
/-- Over a unital star-ring with real scalar action, `stabilizedNegProj` is
`2⁻¹ • (1 - stabilizedConjUnitary)`. -/
theorem stabilizedNegProj_eq_half_one_sub [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
    [SMul ℝ A] (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p)
    (hq : v * v.conjTranspose = q) : stabilizedNegProj v p q =
      (2⁻¹ : ℝ) • (1 - (hv.stabilizedConjUnitary hp hq : CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
  rw [stabilizedNegProj_def, coe_stabilizedConjUnitary, ← fromBlocks_one, fromBlocks_sub]; simp
/-- `stabilizedNegProj v p q` is a star projection when `v` is a partial isometry with initial
projection `p = v.conjTranspose * v` and final projection `q = v * v.conjTranspose`, assuming
compatible real star-algebra scalar hypotheses (`Module ℝ A`, `IsScalarTower ℝ A A`,
`SMulCommClass ℝ A A`, `StarModule ℝ A`) rather than the bare `[SMul ℝ A]` of the definition. -/
theorem isStarProjection_stabilizedNegProj [NonUnitalRing A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    IsStarProjection (stabilizedNegProj v p q) := by
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  have hq_proj : IsStarProjection q := hq ▸ hv.isStarProjection_mul_conjTranspose_self
  refine ⟨?_, by simp [isSelfAdjoint_iff, stabilizedNegProj_def,
    hp_proj.isSelfAdjoint.star_eq, hq_proj.isSelfAdjoint.star_eq]⟩
  rw [IsIdempotentElem, stabilizedNegProj_def, CStarMatrix.smul_mul_smul, fromBlocks_mul]
  simp only [CStarMatrix.neg_mul, CStarMatrix.mul_neg, neg_neg, hp_proj.isIdempotentElem.eq,
    hq_proj.isIdempotentElem.eq, hp, hq, hv.mul_eq_self_of_conjTranspose_mul_self_eq hp,
    hv.mul_conjTranspose_eq_of_conjTranspose_mul_self_eq hp,
    hv.mul_eq_self_of_mul_conjTranspose_self_eq hq,
    hv.conjTranspose_mul_eq_of_mul_conjTranspose_self_eq hq,
    ← two_smul ℝ, fromBlocks_smul, smul_neg, smul_smul]; norm_num
private theorem stabilizedNegProj_mul_fromRows_zero [NonUnitalRing A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) :
    stabilizedNegProj v p q * fromRows p (0 : CStarMatrix n m A) =
      (2⁻¹ : ℝ) • fromRows p (-v) := by
  have hp_idem : p * p = p := (hp ▸ hv.isStarProjection_conjTranspose_mul_self).isIdempotentElem.eq
  rw [stabilizedNegProj_def, CStarMatrix.smul_mul, fromBlocks_mul_fromRows, CStarMatrix.mul_zero,
    _root_.add_zero, CStarMatrix.neg_mul, CStarMatrix.mul_zero, _root_.add_zero, hp_idem,
    hv.mul_eq_self_of_conjTranspose_mul_self_eq hp]
section
variable [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [StarModule ℂ A] (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p)
include hv hp
private theorem stabilizedProjRotRows_mul_conjTranspose (hq : v * v.conjTranspose = q) (t : ℝ) :
    stabilizedProjRotRows v p t * (stabilizedProjRotRows v p t).conjTranspose =
      stabilizedProjRot v p q t := by
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  rw [stabilizedProjRotRows, fromRows_mul_conjTranspose_fromRows, stabilizedProjRot_def]
  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · simp only [conjTranspose_smul, hp_proj.isSelfAdjoint.conjTranspose_eq,
      Complex.star_def, Complex.conj_ofReal, CStarMatrix.smul_mul_smul,
      hp_proj.isIdempotentElem.eq]
    congr 1; ring
  · simp only [conjTranspose_smul, star_mul, star_neg, Complex.star_def, Complex.conj_ofReal,
      Complex.conj_I, neg_neg, CStarMatrix.smul_mul_smul,
      hv.mul_conjTranspose_eq_of_conjTranspose_mul_self_eq hp]
    congr 1; ring
  · simp only [conjTranspose_smul, hp_proj.isSelfAdjoint.conjTranspose_eq,
      Complex.star_def, Complex.conj_ofReal, CStarMatrix.smul_mul_smul,
      hv.mul_eq_self_of_conjTranspose_mul_self_eq hp]
  · simp only [conjTranspose_smul, star_mul, star_neg, Complex.star_def, Complex.conj_ofReal,
      Complex.conj_I, neg_neg, CStarMatrix.smul_mul_smul, hq]
    congr 1; linear_combination -(Real.sin (Real.pi * t / 2) : ℂ) ^ 2 * Complex.I_sq
private theorem isPartialIsometry_stabilizedProjRotRows (t : ℝ) :
    (stabilizedProjRotRows v p t).IsPartialIsometry := by
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  set c : ℂ := ↑(Real.cos (Real.pi * t / 2)); set s : ℂ := ↑(Real.sin (Real.pi * t / 2))
  have htrig : c * c + s * Complex.I * (-Complex.I * s) = 1 := by
    linear_combination (by simp [c, s] : c ^ 2 + s ^ 2 = 1) - s ^ 2 * Complex.I_sq
  have hinit : (stabilizedProjRotRows v p t).conjTranspose * stabilizedProjRotRows v p t = p := by
    rw [stabilizedProjRotRows, conjTranspose_fromRows_mul_fromRows]
    simp only [conjTranspose_smul, hp_proj.isSelfAdjoint.conjTranspose_eq, star_mul, star_neg,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_I, neg_neg, CStarMatrix.smul_mul_smul,
      hp_proj.isIdempotentElem.eq, hp, ← add_smul]
    simpa only [c, s, one_smul] using congrArg (fun z : ℂ => z • p) htrig
  rw [isPartialIsometry_iff, mul_assoc_rectangular, hinit, stabilizedProjRotRows, fromRows_mul,
    CStarMatrix.smul_mul, CStarMatrix.smul_mul, hp_proj.isIdempotentElem.eq,
    hv.mul_eq_self_of_conjTranspose_mul_self_eq hp]
/-- Every point on `stabilizedProjRot v p q` is a star projection when `p = vᴴ * v` and
`q = v * vᴴ` are the initial and final projections of a partial isometry `v`. -/
theorem isStarProjection_stabilizedProjRot (hq : v * v.conjTranspose = q) (t : ℝ) :
    IsStarProjection (stabilizedProjRot v p q t) :=
  hv.stabilizedProjRotRows_mul_conjTranspose hp hq t ▸
    (hv.isPartialIsometry_stabilizedProjRotRows hp t).isStarProjection_mul_conjTranspose_self
end
section
variable [DecidableEq m] [DecidableEq n] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q)
private theorem expUnitary_smul_stabilizedNegProj_mul_fromRows (t : ℝ) :
    ((selfAdjoint.expUnitary ((t * Real.pi) • ⟨stabilizedNegProj v p q,
      (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) * fromRows p (0 : CStarMatrix n m A) =
      (↑(Real.cos (Real.pi * t / 2)) + ↑(Real.sin (Real.pi * t / 2)) * Complex.I) •
        stabilizedProjRotRows v p t := by
  set c : ℂ := ↑(Real.cos (Real.pi * t / 2)); set s : ℂ := ↑(Real.sin (Real.pi * t / 2))
  set z : ℂ := c + s * Complex.I; have hcs : c ^ 2 + s ^ 2 = 1 := by simp [c, s]
  set α : ℂ := (Complex.exp (↑(t * Real.pi) * Complex.I) - 1) * 2⁻¹
  -- Write `exp (i π t) = z ^ 2` with `z = exp (i π t / 2) = c + i s`, so `1 + α = z c` and
  -- `-α = z (-i s)`.
  have harg : (↑(t * Real.pi) * Complex.I : ℂ) = ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I +
      ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hα : α = (z ^ 2 - 1) * 2⁻¹ := by
    simp only [α, harg, Complex.exp_add, Complex.exp_ofReal_mul_I, c, s, z, sq]
  have h1α : 1 + α = z * c := by
    rw [hα]; linear_combination -((1 : ℂ) / 2) * hcs + (s ^ 2 / 2) * Complex.I_sq
  have hnα : -α = z * (-Complex.I * s) := by
    rw [hα]; linear_combination -((1 : ℂ) / 2) * hcs + (s ^ 2 / 2) * Complex.I_sq
  have hcoe : ((selfAdjoint.expUnitary ((t * Real.pi) • ⟨stabilizedNegProj v p q,
      (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      1 + (Complex.exp (↑(t * Real.pi) * Complex.I) - 1) • stabilizedNegProj v p q :=
    (hv.isStarProjection_stabilizedNegProj hp hq).coe_expUnitary_smul (t * Real.pi)
  have hcast : (2⁻¹ : ℝ) • fromRows p (-v) = ((2⁻¹ : ℝ) : ℂ) • fromRows p (-v) :=
    ext fun _ _ => (Complex.coe_smul _ _).symm
  have hα_mul : (Complex.exp (↑(t * Real.pi) * Complex.I) - 1) * ((2⁻¹ : ℝ) : ℂ) = α := by
    rw [Complex.ofReal_inv, Complex.ofReal_ofNat]
  calc
    ((selfAdjoint.expUnitary ((t * Real.pi) • ⟨stabilizedNegProj v p q,
        (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
        CStarMatrix (m ⊕ n) (m ⊕ n) A) * fromRows p (0 : CStarMatrix n m A)
        = (1 + (Complex.exp (↑(t * Real.pi) * Complex.I) - 1) • stabilizedNegProj v p q) *
            fromRows p 0 := by rw [hcoe]
      _ = fromRows p 0 + (Complex.exp (↑(t * Real.pi) * Complex.I) - 1) •
            ((2⁻¹ : ℝ) • fromRows p (-v)) := by
          rw [CStarMatrix.add_mul, CStarMatrix.one_mul, CStarMatrix.smul_mul,
            hv.stabilizedNegProj_mul_fromRows_zero hp]
      _ = fromRows ((1 + α) • p) ((-α) • v) := by
          rw [hcast, smul_smul, hα_mul, fromRows_smul, smul_neg, ← neg_smul,
            fromRows_add, _root_.zero_add]
          congr 1
          rw [add_smul, one_smul]
      _ = z • stabilizedProjRotRows v p t := by
          rw [h1α, hnα, stabilizedProjRotRows, fromRows_smul, smul_smul, smul_smul]
/-- Over a star-ordered unital C⋆-algebra, `selfAdjoint.expUnitary` with generator
`(t * π) • stabilizedNegProj v p q` conjugates `blockSum p 0` to `stabilizedProjRot v p q t`. -/
theorem expUnitary_conj_blockSum_eq_stabilizedProjRot (t : ℝ) :
    ((selfAdjoint.expUnitary ((t * Real.pi) • ⟨stabilizedNegProj v p q,
      (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
      star ((selfAdjoint.expUnitary ((t * Real.pi) • ⟨stabilizedNegProj v p q,
        (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
        CStarMatrix (m ⊕ n) (m ⊕ n) A) = stabilizedProjRot v p q t := by
  set z : ℂ := ↑(Real.cos (Real.pi * t / 2)) + ↑(Real.sin (Real.pi * t / 2)) * Complex.I with hz
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hz, Complex.normSq_add_mul_I]; simp
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  -- Factor `blockSum p 0 = F * Fᴴ` so `U * blockSum p 0 * Uᴴ = (U * F) * (U * F)ᴴ`.
  rw [star_eq_conjTranspose, ← hp_proj.fromRows_zero_mul_conjTranspose_fromRows_zero,
    ← mul_assoc_rectangular, mul_assoc_rectangular (_ * fromRows p 0), ← conjTranspose_mul,
    hv.expUnitary_smul_stabilizedNegProj_mul_fromRows hp hq t, conjTranspose_smul,
    CStarMatrix.smul_mul_smul, hzz, one_smul, hv.stabilizedProjRotRows_mul_conjTranspose hp hq t]
/-- Continuous path `t ↦ expUnitary ((t * π) • stabilizedNegProj v p q)` from `1` to
`stabilizedConjUnitary` over a star-ordered unital C⋆-algebra, built from Mathlib's
`selfAdjoint.expUnitaryPathToOne`. -/
def stabilizedConjUnitaryPath :
    Path (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) (hv.stabilizedConjUnitary hp hq) :=
  (selfAdjoint.expUnitaryPathToOne (Real.pi • ⟨stabilizedNegProj v p q,
    (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩)).cast rfl (by
    refine (Unitary.expUnitary_pi_smul_half_one_sub (hv.stabilizedConjUnitary hp hq)
      (hv.isSelfAdjoint_stabilizedConjUnitary hp hq)).symm.trans ?_
    exact congrArg selfAdjoint.expUnitary
      (congrArg (Real.pi • ·) (Subtype.ext (hv.stabilizedNegProj_eq_half_one_sub hp hq).symm)))
/-- Pointwise exponential evaluation of `stabilizedConjUnitaryPath`. -/
@[simp low] theorem stabilizedConjUnitaryPath_apply (t : unitInterval) :
    hv.stabilizedConjUnitaryPath hp hq t =
      selfAdjoint.expUnitary (((t : ℝ) * Real.pi) • ⟨stabilizedNegProj v p q,
        (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) := by
  rw [stabilizedConjUnitaryPath, Path.cast_coe, selfAdjoint.expUnitaryPathToOne_apply]
  congr 1; exact smul_smul (t : ℝ) Real.pi _
/-- Pointwise conjugation of `blockSum p 0` along `stabilizedConjUnitaryPath` yields
`stabilizedProjRot v p q t`. -/
theorem stabilizedConjUnitaryPath_conj (t : unitInterval) :
    ((hv.stabilizedConjUnitaryPath hp hq t : unitary _) : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
      blockSum p 0 * star ((hv.stabilizedConjUnitaryPath hp hq t : unitary _) :
        CStarMatrix (m ⊕ n) (m ⊕ n) A) = stabilizedProjRot v p q t := by
  rw [hv.stabilizedConjUnitaryPath_apply hp hq t,
    hv.expUnitary_conj_blockSum_eq_stabilizedProjRot hp hq]
end
section
variable [NonUnitalCStarAlgebra A] (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p)
  (hq : v * v.conjTranspose = q)
/-- Continuous path of star projections from `blockSum p 0` to `blockSum 0 q`. -/
def stabilizedProjPath : Path (⟨blockSum p 0, isStarProjection_blockSum_iff.mpr
        ⟨hp ▸ hv.isStarProjection_conjTranspose_mul_self, .zero _⟩⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨blockSum 0 q, isStarProjection_blockSum_iff.mpr
        ⟨.zero _, hq ▸ hv.isStarProjection_mul_conjTranspose_self⟩⟩ :=
  ⟨⟨fun t => ⟨stabilizedProjRot v p q t, hv.isStarProjection_stabilizedProjRot hp hq t⟩,
    ((continuous_stabilizedProjRot v p q).comp continuous_subtypeVal).subtype_mk _⟩,
    Subtype.ext (stabilizedProjRot_zero v p q), Subtype.ext (stabilizedProjRot_one v p q)⟩
@[simp] theorem coe_stabilizedProjPath_apply (t : unitInterval) :
    ((hv.stabilizedProjPath hp hq t : {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P}) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) = stabilizedProjRot v p q t := (rfl)
end
end IsPartialIsometry

section
variable [Fintype m] [Fintype n] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
/-- Equivalent projections are conjugate by a self-adjoint unitary after stabilization. -/
theorem MurrayVonNeumannEquiv.exists_isSelfAdjoint_unitary_conj_blockSum_eq
    [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A] (h : p.MurrayVonNeumannEquiv q) :
    ∃ w : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
      IsSelfAdjoint (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) ∧
      (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
        star (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) = blockSum 0 q :=
  let ⟨_, hv, hp, hq⟩ := h.exists_isPartialIsometry
  ⟨hv.stabilizedConjUnitary hp hq, hv.isSelfAdjoint_stabilizedConjUnitary hp hq,
    hv.stabilizedConjUnitary_conj hp hq⟩
/-- Equivalent projections become unitarily equivalent after stabilization. -/
theorem MurrayVonNeumannEquiv.isUnitarilyEquivalent_blockSum [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] (h : p.MurrayVonNeumannEquiv q) :
    TauCeti.IsUnitarilyEquivalent (blockSum p (0 : CStarMatrix n n A))
      (blockSum (0 : CStarMatrix m m A) q) :=
  let ⟨w, _, hw⟩ := h.exists_isSelfAdjoint_unitary_conj_blockSum_eq
  (TauCeti.isUnitarilyEquivalent_iff
    (isStarProjection_blockSum_iff.mpr ⟨h.isStarProjection_left, .zero _⟩)
    (isStarProjection_blockSum_iff.mpr ⟨.zero _, h.isStarProjection_right⟩)).mpr ⟨w, hw⟩
/-- Over a unital C⋆-algebra, if `p` and `q` are Murray–von Neumann equivalent, a unitary joined
to `1` conjugates `blockSum p 0` to `blockSum 0 q`. -/
theorem MurrayVonNeumannEquiv.exists_joined_one_unitary_conj_blockSum_eq
    [DecidableEq m] [DecidableEq n] [CStarAlgebra A] (h : p.MurrayVonNeumannEquiv q) :
    ∃ w : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A), Joined 1 w ∧
      (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
        star (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) = blockSum 0 q := by
  let _ := CStarAlgebra.spectralOrder A; have _ := CStarAlgebra.spectralOrderedRing A
  obtain ⟨w, hw, hw_conj⟩ := h.exists_isSelfAdjoint_unitary_conj_blockSum_eq
  exact ⟨w, Unitary.joined_one_of_isSelfAdjoint w hw, hw_conj⟩
/-- Equivalent projections over any C⋆-algebra are joined by a path of projections stably. -/
theorem MurrayVonNeumannEquiv.joined_blockSum [NonUnitalCStarAlgebra A]
    (h : p.MurrayVonNeumannEquiv q) : Joined
      (⟨blockSum p 0, isStarProjection_blockSum_iff.mpr ⟨h.isStarProjection_left, .zero _⟩⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨blockSum 0 q, isStarProjection_blockSum_iff.mpr ⟨.zero _, h.isStarProjection_right⟩⟩ :=
  let ⟨_, hv, hp, hq⟩ := h.exists_isPartialIsometry; ⟨hv.stabilizedProjPath hp hq⟩
/-- Equivalent projections over any C⋆-algebra are homotopy equivalent after stabilization. -/
theorem MurrayVonNeumannEquiv.isHomotopicProjection_blockSum [NonUnitalCStarAlgebra A]
    (h : p.MurrayVonNeumannEquiv q) :
    TauCeti.IsHomotopicProjection (blockSum p (0 : CStarMatrix n n A))
      (blockSum (0 : CStarMatrix m m A) q) :=
  (TauCeti.isHomotopicProjection_iff
    (isStarProjection_blockSum_iff.mpr ⟨h.isStarProjection_left, .zero _⟩)
    (isStarProjection_blockSum_iff.mpr ⟨.zero _, h.isStarProjection_right⟩)).mpr h.joined_blockSum
end
end CStarMatrix
