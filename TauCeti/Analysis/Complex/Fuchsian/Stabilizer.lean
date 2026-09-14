/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Analysis.Complex.Fuchsian.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.SmulDeriv
import Mathlib.RingTheory.IntegralDomain
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Point stabilizers of subgroups of `PSL(2, ℝ)`

The transformations fixing a point `z` of the upper half-plane are recorded by their derivative
there. By the chain rule that derivative is multiplicative on the stabilizer, so it is a
character `stabilizer Γ z →* ℂ` for any subgroup `Γ ≤ PSL(2, ℝ)`, and it is injective: a Möbius
transformation fixing `z` with derivative `1` there is the identity. Hence a point stabilizer is
commutative, and cyclic as soon as it is finite — a finite subgroup of the multiplicative monoid
of a field is cyclic.

For a discrete `Γ` the action is properly discontinuous, so every point stabilizer is finite and
therefore finite cyclic: these are the elliptic stabilizers of a Fuchsian group. The injectivity
of the character turns the order of a generator into the order of its derivative, so the
derivative of a generator is a primitive root of unity whose order is the elliptic order of the
point. Finally, every nontrivial element of a point stabilizer is an elliptic matrix.

## Main declarations

* `TauCeti.UpperHalfPlane.stabilizerDeriv`: the derivative character of a point stabilizer, and
  `TauCeti.UpperHalfPlane.stabilizerDeriv_injective`.
* `TauCeti.UpperHalfPlane.isCyclic_stabilizer`: a finite point stabilizer is cyclic; the
  instance below specializes it to a discrete `Γ`, where finiteness is automatic.
* `TauCeti.UpperHalfPlane.exists_isPrimitiveRoot_stabilizerDeriv`: a generator of a finite point
  stabilizer has a primitive root of unity of the stabilizer's order as its derivative.
* `TauCeti.UpperHalfPlane.isElliptic_of_smul_eq_self`: a matrix fixing a point of `ℍ` and
  nontrivial in `PSL(2, ℝ)` is elliptic.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, Chapters 7–8.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of
  Chicago Press, 1992, §§2.1–2.4.
-/

public section

noncomputable section

open Matrix Matrix.SpecialLinearGroup MulAction UpperHalfPlane

open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

/-- An element of `SL(2, ℝ)` that fixes `z : ℍ` and whose automorphy factor at `z` is a real
number `e` is the scalar matrix `e`. Comparing imaginary parts in `c * z + d = e` forces `c = 0`
and hence `d = e`; comparing them in `a * z + b = e * z` then forces `a = e` and hence `b = 0`,
since `z` is not real. -/
theorem coe_eq_scalar_of_smul_eq_self {g : SL(2, ℝ)} {z : ℍ} {e : ℝ} (hz : g • z = z)
    (hd : denom (mapGL ℝ g) (z : ℂ) = (e : ℂ)) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.scalar (Fin 2) e := by
  have hdet : (0 : ℝ) < (mapGL ℝ g).det.val := by simp
  have hne : (e : ℂ) ≠ 0 := hd ▸ denom_ne_zero (mapGL ℝ g) z
  have hn : num (mapGL ℝ g) (z : ℂ) = (e : ℂ) * (z : ℂ) := by
    have h1 : ((mapGL ℝ g) • z : ℍ) = z := hz
    have h2 := coe_smul_of_det_pos hdet z
    rw [h1, hd, eq_div_iff hne] at h2
    rw [← h2]
    ring
  simp only [num, denom, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingHom.id_apply, Algebra.algebraMap_self, Complex.ext_iff, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero] at hd hn
  have him : (z : ℂ).im ≠ 0 := z.im_ne_zero
  have h10 : g 1 0 = 0 := by
    rcases mul_eq_zero.mp (show g 1 0 * (z : ℂ).im = 0 by linarith [hd.2]) with h | h
    · exact h
    · exact absurd h him
  have h00 : g 0 0 = e := by
    rcases mul_eq_zero.mp (show (g 0 0 - e) * (z : ℂ).im = 0 by rw [sub_mul]; linarith [hn.2])
      with h | h
    · linarith
    · exact absurd h him
  have h11 : g 1 1 = e := by
    have h := hd.1
    rw [h10] at h
    linarith
  have h01 : g 0 1 = 0 := by
    have h := hn.1
    rw [h00] at h
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h00, h01, h10, h11]

/-- An element of `SL(2, ℝ)` fixing `z : ℍ` whose automorphy factor at `z` squares to one is
central, that is, `±1`. -/
theorem mem_center_of_denom_sq_eq_one {g : SL(2, ℝ)} {z : ℍ} (hz : g • z = z)
    (hd : denom (mapGL ℝ g) (z : ℂ) ^ 2 = 1) : g ∈ Subgroup.center SL(2, ℝ) := by
  rw [mem_center_iff_eq_one_or_eq_neg_one]
  have hd' : denom (mapGL ℝ g) (z : ℂ) * denom (mapGL ℝ g) (z : ℂ) = 1 := by rw [← sq]; exact hd
  rcases mul_self_eq_one_iff.mp hd' with h | h
  · exact Or.inl (Subtype.ext (by
      rw [coe_eq_scalar_of_smul_eq_self hz (e := 1) (by simpa using h)]; simp))
  · refine Or.inr (Subtype.ext ?_)
    rw [coe_eq_scalar_of_smul_eq_self hz (e := -1) (by simpa using h)]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

/-- **The derivative of the action detects the identity**: a Möbius transformation of `ℍ` fixing
`z` whose derivative at `z` is `1` is the identity of `PSL(2, ℝ)`. -/
theorem eq_one_of_smulDeriv_eq_one {q : PSL(2, ℝ)} {z : ℍ} (hz : q • z = z)
    (h : smulDeriv q z = 1) : q = 1 := by
  induction q using QuotientGroup.induction_on with | _ g =>
  rw [smulDeriv_coe, inv_eq_one] at h
  refine (QuotientGroup.eq_one_iff g).mpr (mem_center_of_denom_sq_eq_one ?_ h)
  rwa [pslMk_smul] at hz

/-- The derivative character of the stabilizer of `z : ℍ` in a subgroup `Γ ≤ PSL(2, ℝ)`: it
sends an element fixing `z` to its derivative at `z`. It is a monoid homomorphism by the chain
rule `TauCeti.UpperHalfPlane.smulDeriv_mul`, the translated point being `z` itself. -/
def stabilizerDeriv (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) : stabilizer Γ z →* ℂ where
  toFun q := smulDeriv ((q : Γ) : PSL(2, ℝ)) z
  map_one' := by simp
  map_mul' q₁ q₂ := by
    have h₂ : (((q₂ : Γ) : PSL(2, ℝ)) • z) = z := q₂.2
    simp only [Subgroup.coe_mul, smulDeriv_mul, h₂]

/-- The derivative character evaluated on an element of the stabilizer. -/
@[simp]
theorem stabilizerDeriv_apply (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (q : stabilizer Γ z) :
    stabilizerDeriv Γ z q = smulDeriv ((q : Γ) : PSL(2, ℝ)) z := (rfl)

/-- **The derivative character of a point stabilizer is injective**: a transformation fixing `z`
is determined by its derivative at `z`. -/
theorem stabilizerDeriv_injective (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    Function.Injective (stabilizerDeriv Γ z) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  exact Subtype.ext (Subtype.ext (eq_one_of_smulDeriv_eq_one q.2 hq))

/-- The derivative character is injective, so a point stabilizer is commutative. -/
instance instIsMulCommutativeStabilizer (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    IsMulCommutative (stabilizer Γ z) where
  is_comm := ⟨fun q₁ q₂ ↦ stabilizerDeriv_injective Γ z (by rw [map_mul, map_mul, mul_comm])⟩

/-- **A finite point stabilizer is cyclic**: the derivative character embeds it into the
multiplicative monoid of `ℂ`, and a finite subgroup of the units of a domain is cyclic. -/
theorem isCyclic_stabilizer (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) [Finite (stabilizer Γ z)] :
    IsCyclic (stabilizer Γ z) :=
  isCyclic_of_injective_ringHom _ (stabilizerDeriv_injective Γ z)

/-- **The point stabilizers of a Fuchsian group are cyclic.** A discrete subgroup of
`PSL(2, ℝ)` acts properly discontinuously, so its point stabilizers are finite, and
`TauCeti.UpperHalfPlane.isCyclic_stabilizer` applies. -/
instance instIsCyclicStabilizer (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) :
    IsCyclic (stabilizer Γ z) :=
  isCyclic_stabilizer Γ z

/-- The order of an element of a point stabilizer is the order of its derivative at that
point. -/
theorem orderOf_stabilizerDeriv (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (q : stabilizer Γ z) :
    orderOf (stabilizerDeriv Γ z q) = orderOf q :=
  orderOf_injective _ (stabilizerDeriv_injective Γ z) q

/-- **A finite point stabilizer is generated by a transformation whose derivative at the point
is a primitive root of unity** of order the stabilizer's order — the elliptic order of the
point. -/
theorem exists_isPrimitiveRoot_stabilizerDeriv (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    [Finite (stabilizer Γ z)] :
    ∃ q : stabilizer Γ z, Subgroup.zpowers q = ⊤ ∧
      IsPrimitiveRoot (stabilizerDeriv Γ z q) (Nat.card (stabilizer Γ z)) := by
  obtain ⟨q, hq⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (isCyclic_stabilizer Γ z)
  refine ⟨q, hq, ?_⟩
  have hcard : orderOf q = Nat.card (stabilizer Γ z) := by
    rw [← Nat.card_zpowers, hq, Subgroup.card_top]
  rw [← hcard, ← orderOf_stabilizerDeriv]
  exact IsPrimitiveRoot.orderOf _

/-- **A nontrivial point stabilizer consists of elliptic matrices**: an element of `SL(2, ℝ)`
fixing a point of `ℍ` and not central is elliptic, its trace being too small for real
eigenvalues. -/
theorem isElliptic_of_smul_eq_self {g : SL(2, ℝ)} {z : ℍ} (hz : g • z = z)
    (hg : (g : PSL(2, ℝ)) ≠ 1) : Matrix.GeneralLinearGroup.IsElliptic (mapGL ℝ g) := by
  refine isElliptic_of_exists_smul_eq_self (by simp) (fun hc ↦ hg ?_) ⟨z, hz⟩
  have h := forall_smul_eq_self_iff_mem_center.mpr hc
  exact eq_of_smul_eq_smul fun w : ℍ ↦ by rw [one_smul, pslMk_smul]; exact h w

end TauCeti.UpperHalfPlane
