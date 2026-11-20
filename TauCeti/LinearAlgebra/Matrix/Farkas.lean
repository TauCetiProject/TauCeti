/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import TauCeti.Geometry.Convex.Cone.FiniteDuality
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Farkas certificates for finite systems of linear equations and inequalities

Over a linearly ordered field `K`, consider a finite system `A *ᵥ x ≤ b`, `E *ᵥ x = d` in the
unknown `x : ι → K`. Multiplying the inequalities by `y ≥ 0`, the equations by an arbitrary `z`,
and adding gives the consequence `(y ᵥ* A + z ᵥ* E) ⬝ᵥ x ≤ y ⬝ᵥ b + z ⬝ᵥ d`. Farkas' lemma says
that these combinations are the only obstructions and the only valid inequalities:

* the system is solvable iff `0 ≤ y ⬝ᵥ b + z ⬝ᵥ d` whenever `y ≥ 0` and `y ᵥ* A + z ᵥ* E = 0`
  (`Matrix.exists_mulVec_le_and_mulVec_eq_iff`); otherwise such a pair `(y, z)` is an
  infeasibility certificate;
* for a solvable system, `c ⬝ᵥ x ≤ δ` holds on every solution iff `c = y ᵥ* A + z ᵥ* E` and
  `y ⬝ᵥ b + z ⬝ᵥ d ≤ δ` for some `y ≥ 0` and `z`
  (`Matrix.exists_vecMul_add_vecMul_eq_and_le_iff`), with the homogeneous special case
  `Matrix.exists_vecMul_add_vecMul_eq_iff`.

The equality multipliers `z` are unrestricted in sign. Encoding each equation as two opposite
inequalities would recover them, but the statements here keep equations and inequalities apart, as
linear systems coming from combinatorics (normalizations, prescribed boundaries) usually present
them.

Since certificates are finite linear-algebra data, they transport along any order-preserving ring
homomorphism `f : K →+*o L` of linearly ordered fields; hence a system with coefficients in `K` is
solvable over `L` iff it is solvable over `K` (`Matrix.exists_mulVec_le_and_mulVec_eq_map_iff`).
For `K = ℚ` this produces rational solutions of rational systems that are solvable over `ℝ`.

The proofs apply the algebraic separation theorem for finitely generated cones,
`Submodule.FG.exists_cone_dual_nonneg_and_lt_zero` (a consequence of Tucker's theorem of the
alternative), to the cone in `(ι → K) × K` spanned by the rows `(A i, b i)`, `±(E j, d j)` and
`(0, 1)`. No topology is used, so everything holds over `ℚ`.

## Main results

* `Matrix.vecMul_add_vecMul_dotProduct_le`: weak duality, over any ordered semiring.
* `Matrix.exists_mulVec_le_and_mulVec_eq_iff`: Farkas' lemma for mixed systems.
* `Matrix.exists_dual_of_not_exists_vecMul_add_vecMul_eq_and_le`: a separating certificate for
  an inequality that is not a nonnegative combination of the system.
* `Matrix.exists_vecMul_add_vecMul_eq_and_le_iff`: valid inequalities of a solvable system.
* `Matrix.exists_vecMul_add_vecMul_eq_iff`: valid homogeneous inequalities.
* `Matrix.exists_mulVec_le_and_mulVec_eq_map_iff`: solvability is invariant under ordered field
  extension.

## References

* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, §7.3, Corollaries 7.1d
  and 7.1h.
-/

public section

open Matrix

namespace Matrix

section Ordered

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  {m p ι : Type*} [Fintype m] [Fintype p] [Fintype ι]

/-- **Weak duality.** On a solution of `A *ᵥ x ≤ b`, `E *ᵥ x = d`, every combination of the rows
with nonnegative inequality multipliers `y` and arbitrary equality multipliers `z` is bounded by
the same combination of the right-hand sides. -/
theorem vecMul_add_vecMul_dotProduct_le {A : Matrix m ι R} {b : m → R} {E : Matrix p ι R}
    {d : p → R} {x : ι → R} (hA : A *ᵥ x ≤ b) (hE : E *ᵥ x = d) {y : m → R} (hy : 0 ≤ y)
    (z : p → R) : (y ᵥ* A + z ᵥ* E) ⬝ᵥ x ≤ y ⬝ᵥ b + z ⬝ᵥ d := by
  rw [add_dotProduct, ← dotProduct_mulVec, ← dotProduct_mulVec, hE]
  exact add_le_add_left (dotProduct_le_dotProduct_of_nonneg_left hA hy) _

end Ordered

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L]
  {m p ι : Type*} [Fintype m] [Fintype p] [Fintype ι]

/-- The generators of the cone of consequences of `A *ᵥ x ≤ b`, `E *ᵥ x = d`: the rows
`(A i, b i)`, the rows `±(E j, d j)` and `(0, 1)`. -/
private def farkasGenerators (A : Matrix m ι K) (b : m → K) (E : Matrix p ι K) (d : p → K) :
    m ⊕ p ⊕ p ⊕ Unit → (ι → K) × K :=
  Sum.elim (fun i => (A i, b i))
    (Sum.elim (fun j => (E j, d j)) (Sum.elim (fun j => -(E j, d j)) fun _ => (0, 1)))

omit [Fintype ι] in
/-- A point `(c, δ)` of the cone spanned by `farkasGenerators` is a combination
`y ᵥ* A + z ᵥ* E = c`, `y ⬝ᵥ b + z ⬝ᵥ d ≤ δ` with `y ≥ 0`. -/
private theorem exists_of_mem_hull_farkasGenerators {A : Matrix m ι K} {b : m → K}
    {E : Matrix p ι K} {d : p → K} {c : ι → K} {δ : K}
    (hmem : (c, δ) ∈ PointedCone.hull K (Set.range (farkasGenerators A b E d))) :
    ∃ (y : m → K) (z : p → K), 0 ≤ y ∧ y ᵥ* A + z ᵥ* E = c ∧ y ⬝ᵥ b + z ⬝ᵥ d ≤ δ := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp ha
  refine ⟨fun i => a (.inl i), fun j => a (.inr (.inl j)) - a (.inr (.inr (.inl j))),
    fun i => (a (.inl i)).2, ?_, ?_⟩
  · ext k
    simp [farkasGenerators, Fintype.sum_sum_type, Prod.fst_sum, Finset.sum_apply, vecMul,
      dotProduct, sub_eq_add_neg, mul_add, Finset.sum_add_distrib, mul_comm, ← Nonneg.coe_smul]
  · have h0 := (a (.inr (.inr (.inr ())))).2
    simp [farkasGenerators, Fintype.sum_sum_type, Prod.snd_sum, dotProduct, sub_mul,
      ← Nonneg.coe_smul]
    linarith

/-- **Farkas certificate** for an inequality that is not a combination of a finite system: if
`(c, δ)` is not a combination `y ᵥ* A + z ᵥ* E = c`, `y ⬝ᵥ b + z ⬝ᵥ d ≤ δ` with `y ≥ 0`, then some
`(u, s)` with `s ≥ 0` pairs nonnegatively with every row `(A i, b i)`, vanishes on every row
`(E j, d j)`, and pairs negatively with `(c, δ)`. No solvability of the system is assumed. -/
theorem exists_dual_of_not_exists_vecMul_add_vecMul_eq_and_le (A : Matrix m ι K) (b : m → K)
    (E : Matrix p ι K) (d : p → K) (c : ι → K) (δ : K)
    (h : ¬∃ (y : m → K) (z : p → K), 0 ≤ y ∧ y ᵥ* A + z ᵥ* E = c ∧ y ⬝ᵥ b + z ⬝ᵥ d ≤ δ) :
    ∃ (u : ι → K) (s : K), 0 ≤ s ∧ (∀ i, 0 ≤ A i ⬝ᵥ u + s * b i) ∧
      (∀ j, E j ⬝ᵥ u + s * d j = 0) ∧ c ⬝ᵥ u + s * δ < 0 := by
  classical
  let g := farkasGenerators A b E d
  let C : PointedCone K ((ι → K) × K) := PointedCone.hull K (Set.range g)
  have hC : C.FG := Submodule.fg_span (Set.finite_range g)
  have hnot : (c, δ) ∉ C := fun hmem => h (exists_of_mem_hull_farkasGenerators hmem)
  obtain ⟨f, hf, hfc⟩ := hC.exists_cone_dual_nonneg_and_lt_zero hnot
  have hgC (k) : 0 ≤ f (g k) := hf _ (PointedCone.subset_hull (Set.mem_range_self k))
  set s := f (0, 1)
  set u : ι → K := fun k => f (Pi.single k 1, 0)
  have hf_apply (v : ι → K) (t : K) : f (v, t) = v ⬝ᵥ u + t * s :=
    f.apply_prod_eq_dotProduct_add_mul v t
  have h₀ := hgC (.inr (.inr (.inr ())))
  simp only [g, farkasGenerators, Sum.elim_inr] at h₀
  refine ⟨u, s, h₀, fun i => ?_, fun j => ?_, ?_⟩
  · have := hgC (.inl i)
    simp only [g, farkasGenerators, Sum.elim_inl, hf_apply] at this
    rwa [mul_comm] at this
  · have h₁ := hgC (.inr (.inl j))
    have h₂ := hgC (.inr (.inr (.inl j)))
    simp only [g, farkasGenerators, Sum.elim_inl, Sum.elim_inr, Prod.neg_mk, hf_apply,
      neg_dotProduct] at h₁ h₂
    linarith
  · rw [hf_apply] at hfc
    linarith

omit [Fintype m] [Fintype p] in
/-- Rescaling step: a separating vector `(u, s)` with `s > 0` yields the solution `-s⁻¹ • u`. -/
private theorem mulVec_neg_inv_smul {A : Matrix m ι K} {b : m → K} {E : Matrix p ι K}
    {d : p → K} {u : ι → K} {s : K} (hs : 0 < s) (hA : ∀ i, 0 ≤ A i ⬝ᵥ u + s * b i)
    (hE : ∀ j, E j ⬝ᵥ u + s * d j = 0) :
    A *ᵥ (-s⁻¹ • u) ≤ b ∧ E *ᵥ (-s⁻¹ • u) = d := by
  have key (v : ι → K) (t : K) : v ⬝ᵥ (-s⁻¹ • u) = t - s⁻¹ * (v ⬝ᵥ u + s * t) := by
    rw [dotProduct_smul, smul_eq_mul]
    field_simp
    ring
  refine ⟨fun i => ?_, funext fun j => ?_⟩
  · rw [mulVec, key (A i) (b i)]
    exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr hs.le) (hA i))
  · rw [mulVec, key (E j) (d j), hE j, mul_zero, sub_zero]

/-- **Farkas' lemma** for a finite system of linear inequalities `A *ᵥ x ≤ b` and equations
`E *ᵥ x = d` over a linearly ordered field: the system has a solution iff every combination with
nonnegative inequality multipliers `y` and unrestricted equality multipliers `z` that annihilates
the coefficients, `y ᵥ* A + z ᵥ* E = 0`, has `0 ≤ y ⬝ᵥ b + z ⬝ᵥ d`. -/
theorem exists_mulVec_le_and_mulVec_eq_iff (A : Matrix m ι K) (b : m → K) (E : Matrix p ι K)
    (d : p → K) :
    (∃ x, A *ᵥ x ≤ b ∧ E *ᵥ x = d) ↔
      ∀ (y : m → K) (z : p → K), 0 ≤ y → y ᵥ* A + z ᵥ* E = 0 → 0 ≤ y ⬝ᵥ b + z ⬝ᵥ d := by
  refine ⟨fun ⟨x, hA, hE⟩ y z hy hyz => ?_, fun H => ?_⟩
  · simpa [hyz] using vecMul_add_vecMul_dotProduct_le hA hE hy z
  · by_contra hx
    obtain ⟨u, s, -, hA, hE, hs⟩ :=
      exists_dual_of_not_exists_vecMul_add_vecMul_eq_and_le A b E d 0 (-1)
        fun ⟨y, z, hy, hyz, hle⟩ => (H y z hy hyz).not_gt (by linarith)
    exact hx ⟨_, mulVec_neg_inv_smul (by simpa using hs) hA hE⟩

/-- **Valid inequalities** of a solvable finite system `A *ᵥ x ≤ b`, `E *ᵥ x = d` over a
linearly ordered field: `c ⬝ᵥ x ≤ δ` holds for every solution iff it is implied by a combination of
the system with nonnegative inequality multipliers and unrestricted equality multipliers. -/
theorem exists_vecMul_add_vecMul_eq_and_le_iff {A : Matrix m ι K} {b : m → K}
    {E : Matrix p ι K} {d : p → K} (hsol : ∃ x, A *ᵥ x ≤ b ∧ E *ᵥ x = d) (c : ι → K) (δ : K) :
    (∃ (y : m → K) (z : p → K), 0 ≤ y ∧ y ᵥ* A + z ᵥ* E = c ∧ y ⬝ᵥ b + z ⬝ᵥ d ≤ δ) ↔
      ∀ x, A *ᵥ x ≤ b → E *ᵥ x = d → c ⬝ᵥ x ≤ δ := by
  refine ⟨fun ⟨y, z, hy, hyz, hle⟩ x hA hE => ?_, fun H => ?_⟩
  · exact hyz ▸ (vecMul_add_vecMul_dotProduct_le hA hE hy z).trans hle
  by_contra hcert
  obtain ⟨u, s, hs, hA, hE, hc⟩ :=
    exists_dual_of_not_exists_vecMul_add_vecMul_eq_and_le A b E d c δ hcert
  rcases hs.lt_or_eq with hs | rfl
  · -- A positive last coordinate rescales to a solution `-s⁻¹ • u` violating `c ⬝ᵥ x ≤ δ`.
    have hcx := H _ (mulVec_neg_inv_smul hs hA hE).1 (mulVec_neg_inv_smul hs hA hE).2
    rw [dotProduct_smul, smul_eq_mul] at hcx
    have : δ < -s⁻¹ * (c ⬝ᵥ u) := by
      rw [← mul_lt_mul_iff_of_pos_left hs]
      field_simp
      linarith
    exact hcx.not_gt this
  · -- Otherwise `-u` is a recession direction along which `c ⬝ᵥ x` grows without bound.
    obtain ⟨x₀, hA₀, hE₀⟩ := hsol
    simp only [zero_mul, add_zero] at hA hE hc
    set t : K := (|δ - c ⬝ᵥ x₀| + 1) / -(c ⬝ᵥ u)
    have ht : 0 ≤ t := div_nonneg (by positivity) (by linarith)
    have htu : t * c ⬝ᵥ u = -(|δ - c ⬝ᵥ x₀| + 1) := by
      simp only [t]
      field_simp [hc.ne]
    have hcx := H (x₀ - t • u) (fun i => ?_) (funext fun j => ?_)
    · rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, htu] at hcx
      linarith [le_abs_self (δ - c ⬝ᵥ x₀)]
    · rw [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      -- `(A *ᵥ u) i` unfolds to `A i ⬝ᵥ u`.
      have hAu : 0 ≤ t * (A *ᵥ u) i := mul_nonneg ht (hA i)
      linarith [hA₀ i]
    · rw [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hE₀, mulVec, hE j,
        mul_zero, sub_zero]

/-- **Farkas' lemma**, homogeneous form: the linear inequality `c ⬝ᵥ x ≤ 0` holds on the
polyhedral cone `A *ᵥ x ≤ 0`, `E *ᵥ x = 0` iff `c = y ᵥ* A + z ᵥ* E` for some `y ≥ 0` and `z`. -/
theorem exists_vecMul_add_vecMul_eq_iff (A : Matrix m ι K) (E : Matrix p ι K) (c : ι → K) :
    (∃ (y : m → K) (z : p → K), 0 ≤ y ∧ y ᵥ* A + z ᵥ* E = c) ↔
      ∀ x, A *ᵥ x ≤ 0 → E *ᵥ x = 0 → c ⬝ᵥ x ≤ 0 := by
  rw [← exists_vecMul_add_vecMul_eq_and_le_iff ⟨0, by simp, by simp⟩ c 0]
  simp

omit [IsStrictOrderedRing K] [IsStrictOrderedRing L] [Fintype m] [Fintype p] [Fintype ι] in
private theorem map_dotProduct_orderRingHom (f : K →+*o L) {κ : Type*} [Fintype κ]
    (v w : κ → K) : f (v ⬝ᵥ w) = (f ∘ v) ⬝ᵥ (f ∘ w) := by
  simpa using RingHom.map_dotProduct (f : K →+* L) v w

omit [Fintype m] [Fintype p] in
/-- A finite system of linear inequalities and equations with coefficients in `K` is solvable
over an ordered field extension `f : K →+*o L` iff it is solvable over `K`. -/
theorem exists_mulVec_le_and_mulVec_eq_map_iff [Finite m] [Finite p] (f : K →+*o L)
    (A : Matrix m ι K) (b : m → K) (E : Matrix p ι K) (d : p → K) :
    (∃ x : ι → L, A.map f *ᵥ x ≤ f ∘ b ∧ E.map f *ᵥ x = f ∘ d) ↔
      ∃ x : ι → K, A *ᵥ x ≤ b ∧ E *ᵥ x = d := by
  cases nonempty_fintype m
  cases nonempty_fintype p
  have hmono : StrictMono f :=
    (OrderHomClass.mono f).strictMono_of_injective (f : K →+* L).injective
  refine ⟨fun hL => ?_, fun ⟨x, hA, hE⟩ => ⟨f ∘ x, fun i => ?_, funext fun j => ?_⟩⟩
  · rw [exists_mulVec_le_and_mulVec_eq_iff] at hL ⊢
    intro y z hy hyz
    have hyz' : (f ∘ y) ᵥ* A.map f + (f ∘ z) ᵥ* E.map f = 0 := by
      ext k
      simpa [vecMul, map_dotProduct_orderRingHom, Function.comp_def] using
        congrArg f (congrFun hyz k)
    have := hL (f ∘ y) (f ∘ z) (fun i => by simpa using OrderHomClass.mono f (hy i)) hyz'
    rw [← hmono.le_iff_le, map_zero, map_add, map_dotProduct_orderRingHom,
      map_dotProduct_orderRingHom]
    exact this
  · simpa [mulVec, map_dotProduct_orderRingHom, Function.comp_def] using
      OrderHomClass.mono f (hA i)
  · simpa [mulVec, map_dotProduct_orderRingHom, Function.comp_def] using
      congrArg f (congrFun hE j)

end Matrix
