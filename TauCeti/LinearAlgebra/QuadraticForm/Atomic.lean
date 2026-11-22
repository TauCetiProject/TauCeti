/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Binary
import Mathlib.Data.Fin.Tuple.Sort
import TauCeti.LinearAlgebra.BilinearForm.Ideals
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import TauCeti.LinearAlgebra.BilinearForm.Modular
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.Submodule.Compl
import TauCeti.RingTheory.Valuation.FinsetDvd

/-!
# Atomic normal forms of quadratic forms over a discrete valuation ring

Let `R` be a discrete valuation ring with valuation `v` and uniformizer `π`. Following Voight, a
quadratic form over `R` is **atomic** (`QuadraticMap.IsAtomic`) when it is either a unary form
`⟨a⟩ = a x²` with `a` a unit, or, when `2` is not a unit of `R`, a binary form
`[a, b, c] = a x² + b x y + c y²` with `v(b) < v(2a) ≤ v(2c)` and `a` or `b` a unit. These are
statements about the quadratic map itself: its polar pairing `B(x, y) = q(x + y) - q(x) - q(y)` is
never divided by `2`, and no assumption is made on the characteristic of `R` or of its residue
field.

The main theorem (`QuadraticMap.exists_atomic_normal_form`) says that every quadratic form on a
finite projective `R`-module is an orthogonal sum `π^{e₁} Q₁ ⊥ ⋯ ⊥ π^{e_s} Q_s ⊥ 0` of uniformizer
powers of atomic forms, with `e₁ ≤ ⋯ ≤ e_s`, and of a summand on which the form vanishes (the
blocks of infinite exponent). The decomposition is not unique, and the coefficients of an atomic
presentation are not isometry invariants. This is the local normal form from which the local
theory of integral quadratic lattices, including the dyadic and characteristic-two cases, starts:
when `2` is a unit it is a diagonalization, and at a dyadic place it keeps the binary blocks, such
as the hyperbolic plane `x y` over `ℤ₂`, that admit no orthogonal basis.

The proof is by induction on the rank. If the polar pairing vanishes, a basis vector splits off a
unary or a zero block. Otherwise a value `B(u, w)` of minimal valuation divides every value of the
pairing; if some self-pairing `B(x, x)` has the same valuation, `x` splits off a unary block
(`LinearMap.BilinForm.isCompl_span_singleton_orthogonal_of_dvd`), and if none does, `u` and `w`
span a `B(u, w)`-modular plane which splits off a binary block
(`LinearMap.BilinForm.IsModular.isCompl_orthogonal`). In the second case `2` cannot be a unit,
since otherwise `B(u + w, u + w)` would have the valuation of `B(u, w)`.

## Main definitions

* `QuadraticMap.IsAtomic`: Voight's atomic unary and dyadic binary forms.

## Main results

* `QuadraticMap.isAtomic_binaryQuadraticForm`: when `2` is not a unit, the binary forms
  `a x² + x y + c y²` with `a ∣ c`, among them the hyperbolic plane `x y`, are atomic.
* `QuadraticMap.IsAtomic.exists_eq_mul_sq_of_isUnit_two`: when `2` is a unit, atomic forms are
  unary.
* `QuadraticMap.exists_atomic_normal_form`: the atomic normal form.

## References

* J. Voight, *Quaternion algebras*, Graduate Texts in Mathematics 288, Springer, 2021,
  Definition 9.8.1, Example 9.8.2 and Proposition 9.8.4.
-/

public section

open Module IsDiscreteValuationRing

namespace QuadraticMap

variable {R M N : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A quadratic form over a discrete valuation ring is **atomic** when, in suitable coordinates,
it is either the unary form `⟨a⟩ = a x²` with `a` a unit, or, when `2` is not a unit, the binary
form `[a, b, c] = a x² + b x y + c y²` with `v(b) < v(2a) ≤ v(2c)` and `a` or `b` a unit, where `v`
is the additive valuation. -/
def IsAtomic (Q : QuadraticForm R M) : Prop :=
  (∃ (a : R) (e : M ≃ₗ[R] R), IsUnit a ∧ ∀ x, Q x = a * e x ^ 2) ∨
    ¬IsUnit (2 : R) ∧ ∃ (a b c : R) (e : M ≃ₗ[R] Fin 2 → R),
      addVal R b < addVal R (2 * a) ∧ addVal R (2 * a) ≤ addVal R (2 * c) ∧
      (IsUnit a ∨ IsUnit b) ∧ ∀ x, Q x = a * e x 0 ^ 2 + b * e x 0 * e x 1 + c * e x 1 ^ 2

variable {Q : QuadraticForm R M}

/-- A unary form `a x²` with `a` a unit is atomic. -/
theorem IsAtomic.of_unary {a : R} (e : M ≃ₗ[R] R) (ha : IsUnit a) (h : ∀ x, Q x = a * e x ^ 2) :
    Q.IsAtomic :=
  .inl ⟨a, e, ha, h⟩

/-- When `2` is not a unit, a binary form `a x² + b x y + c y²` with `v(b) < v(2a) ≤ v(2c)` and
`a` or `b` a unit is atomic. -/
theorem IsAtomic.of_binary (h2 : ¬IsUnit (2 : R)) {a b c : R} (e : M ≃ₗ[R] Fin 2 → R)
    (hab : addVal R b < addVal R (2 * a)) (hac : addVal R (2 * a) ≤ addVal R (2 * c))
    (hu : IsUnit a ∨ IsUnit b)
    (h : ∀ x, Q x = a * e x 0 ^ 2 + b * e x 0 * e x 1 + c * e x 1 ^ 2) : Q.IsAtomic :=
  .inr ⟨h2, a, b, c, e, hab, hac, hu, h⟩

/-- When `2` is a unit, an atomic form is unary. -/
theorem IsAtomic.exists_eq_mul_sq_of_isUnit_two (hQ : Q.IsAtomic) (h2 : IsUnit (2 : R)) :
    ∃ (a : R) (e : M ≃ₗ[R] R), IsUnit a ∧ ∀ x, Q x = a * e x ^ 2 :=
  hQ.resolve_right fun h ↦ h.1 h2

/-- An atomic form lives on a module of rank one or two. -/
theorem IsAtomic.finrank_eq_one_or_two (hQ : Q.IsAtomic) :
    finrank R M = 1 ∨ finrank R M = 2 := by
  rcases hQ with ⟨-, e, -, -⟩ | ⟨-, -, -, -, e, -⟩
  · exact .inl (by rw [e.finrank_eq, finrank_self])
  · exact .inr (by rw [e.finrank_eq, finrank_fin_fun])

/-- The form on the zero module is not atomic. -/
theorem not_isAtomic_of_subsingleton [Subsingleton M] (Q : QuadraticForm R M) : ¬Q.IsAtomic :=
  fun hQ ↦ by
    rcases hQ.finrank_eq_one_or_two with h | h <;> simp [finrank_zero_of_subsingleton] at h

/-- Atomicity is invariant under a linear change of coordinates. -/
theorem IsAtomic.comp (hQ : Q.IsAtomic) (f : N ≃ₗ[R] M) :
    (Q.comp (f : N →ₗ[R] M)).IsAtomic := by
  rcases hQ with ⟨a, e, ha, h⟩ | ⟨h2, a, b, c, e, hab, hac, hu, h⟩
  · exact .of_unary (f.trans e) ha fun x ↦ h (f x)
  · exact .of_binary h2 (f.trans e) hab hac hu fun x ↦ h (f x)

/-- When `2` is not a unit, the binary form `a x² + x y + c y²` with `a ∣ c` is atomic. This
includes the hyperbolic plane `x y` (`a = c = 0`), which has no orthogonal basis over `ℤ₂`, and
the form `x² + x y + y²`. -/
theorem isAtomic_binaryQuadraticForm (h2 : ¬IsUnit (2 : R)) {a c : R} (hac : a ∣ c) :
    (TauCeti.binaryQuadraticForm R a c).IsAtomic := by
  refine .of_binary h2 (b := 1) (LinearEquiv.refl R _) ?_
    (addVal_le_iff_dvd.mpr (mul_dvd_mul_left 2 hac)) (.inr isUnit_one) fun x ↦ ?_
  · rw [addVal_one, pos_iff_ne_zero, Ne, addVal_eq_zero_iff]
    exact fun h ↦ h2 (isUnit_of_mul_isUnit_left h)
  · simp only [TauCeti.binaryQuadraticForm_apply, LinearEquiv.refl_apply]
    ring

/-! ### Orthogonal decompositions into atomic blocks -/

/-- `q` is an orthogonal sum of uniformizer powers `π ^ exponent i` of atomic blocks and of a
summand on which it vanishes, with blocks and zero coordinates indexed by arbitrary finite types.
-/
private def HasAtomicDecomposition (π : R) (q : QuadraticForm R M) : Prop :=
  ∃ (ι κ : Type) (_ : Fintype ι) (_ : Fintype κ) (size exponent : ι → ℕ)
    (blocks : (i : ι) → QuadraticForm R (Fin (size i) → R))
    (e : M ≃ₗ[R] ((i : ι) → Fin (size i) → R) × (κ → R)),
    (∀ i, (blocks i).IsAtomic) ∧ ∀ x, q x = ∑ i, π ^ exponent i * blocks i ((e x).1 i)

variable {π : R}

/-- A form vanishing on a free module of finite rank has an atomic decomposition with no
blocks. -/
private theorem HasAtomicDecomposition.of_forall_eq_zero (π : R) {q : QuadraticForm R M} {n : ℕ}
    (b : Basis (Fin n) R M) (hq : ∀ x, q x = 0) : HasAtomicDecomposition π q :=
  ⟨Empty, Fin n, inferInstance, inferInstance, Empty.elim, Empty.elim, fun i ↦ i.elim,
    b.equivFun.trans LinearEquiv.uniqueProd.symm, fun i ↦ i.elim, fun x ↦ by simp [hq]⟩

/-- A uniformizer power of an atomic form is a decomposition with a single block. -/
private theorem HasAtomicDecomposition.of_isAtomic {q : QuadraticForm R M} {k : ℕ}
    {Q : QuadraticForm R (Fin k → R)} (hQ : Q.IsAtomic) (f : M ≃ₗ[R] Fin k → R) (m : ℕ)
    (hq : ∀ x, q x = π ^ m * Q (f x)) : HasAtomicDecomposition π q :=
  ⟨Unit, Empty, inferInstance, inferInstance, fun _ ↦ k, fun _ ↦ m, fun _ ↦ Q,
    f.trans ((LinearEquiv.piUnique R fun _ : Unit ↦ Fin k → R).symm.trans
      LinearEquiv.prodUnique.symm), fun _ ↦ hQ, fun x ↦ by simp [hq]⟩

/-- Decompositions of two forms combine to a decomposition of their orthogonal sum. -/
private theorem HasAtomicDecomposition.prod {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] {q : QuadraticForm R M} {q₁ : QuadraticForm R M₁}
    {q₂ : QuadraticForm R M₂} (f : M ≃ₗ[R] M₁ × M₂) (hf : ∀ x, q x = q₁ (f x).1 + q₂ (f x).2)
    (h₁ : HasAtomicDecomposition π q₁) (h₂ : HasAtomicDecomposition π q₂) :
    HasAtomicDecomposition π q := by
  obtain ⟨ι₁, κ₁, _, _, size₁, exponent₁, blocks₁, e₁, hb₁, he₁⟩ := h₁
  obtain ⟨ι₂, κ₂, _, _, size₂, exponent₂, blocks₂, e₂, hb₂, he₂⟩ := h₂
  let size : ι₁ ⊕ ι₂ → ℕ := Sum.elim size₁ size₂
  let blocks : (i : ι₁ ⊕ ι₂) → QuadraticForm R (Fin (size i) → R)
    | .inl i => blocks₁ i
    | .inr i => blocks₂ i
  refine ⟨ι₁ ⊕ ι₂, κ₁ ⊕ κ₂, inferInstance, inferInstance, size, Sum.elim exponent₁ exponent₂,
    blocks, f.trans <| (e₁.prodCongr e₂).trans <| (LinearEquiv.prodProdProdComm R _ _ _ _).trans <|
      (LinearEquiv.sumPiEquivProdPi R ι₁ ι₂ fun i ↦ Fin (size i) → R).symm.prodCongr
        (LinearEquiv.sumArrowLequivProdArrow κ₁ κ₂ R R).symm,
    fun | .inl i => hb₁ i | .inr i => hb₂ i, fun x ↦ ?_⟩
  rw [hf, he₁, he₂, Fintype.sum_sum_type]
  rfl

/-- Decompositions of the restrictions of a form to two complementary orthogonal submodules
combine to a decomposition of the form. -/
private theorem HasAtomicDecomposition.of_isCompl {q : QuadraticForm R M} {S S' : Submodule R M}
    (hc : IsCompl S S') (horth : ∀ x ∈ S, ∀ y ∈ S', polar q x y = 0)
    (h : HasAtomicDecomposition π (q.comp S.subtype))
    (h' : HasAtomicDecomposition π (q.comp S'.subtype)) : HasAtomicDecomposition π q := by
  refine .prod (S.prodEquivOfIsCompl S' hc).symm (fun x ↦ ?_) h h'
  obtain ⟨y, rfl⟩ := (S.prodEquivOfIsCompl S' hc).surjective x
  have hy := horth _ y.1.property _ y.2.property
  simp [Submodule.coe_prodEquivOfIsCompl', QuadraticMap.map_add q, hy]

/-- A decomposition with arbitrary finite index types can be reindexed by `Fin` with monotone
exponents. -/
private theorem HasAtomicDecomposition.exists_monotone {q : QuadraticForm R M}
    (h : HasAtomicDecomposition π q) :
    ∃ (s z : ℕ) (size exponent : Fin s → ℕ)
      (blocks : (i : Fin s) → QuadraticForm R (Fin (size i) → R))
      (e : M ≃ₗ[R] ((i : Fin s) → Fin (size i) → R) × (Fin z → R)),
      Monotone exponent ∧ (∀ i, size i = 1 ∨ size i = 2) ∧ (∀ i, (blocks i).IsAtomic) ∧
      ∀ x, q x = ∑ i, π ^ exponent i * blocks i ((e x).1 i) := by
  obtain ⟨ι, κ, _, _, size, exponent, blocks, e, hb, he⟩ := h
  let g : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let σ : Fin (Fintype.card ι) ≃ ι := (Tuple.sort (exponent ∘ g)).trans g
  refine ⟨Fintype.card ι, Fintype.card κ, size ∘ σ, exponent ∘ σ, fun i ↦ blocks (σ i),
    e.trans ((LinearEquiv.piCongrLeft R (fun i ↦ Fin (size i) → R) σ).symm.prodCongr
      (LinearEquiv.funCongrLeft R R (Fintype.equivFin κ).symm)),
    Tuple.monotone_sort (exponent ∘ g), fun i ↦ ?_, fun i ↦ hb (σ i), fun x ↦ ?_⟩
  · simpa using (hb (σ i)).finrank_eq_one_or_two
  · rw [he, ← Equiv.sum_comp σ]
    rfl

/-! ### Splitting off a block -/

section Split

variable {q : QuadraticForm R M}

/-- The restriction of `q` to the line spanned by a linearly independent vector `v` is a unary
atomic block or zero. -/
private theorem hasAtomicDecomposition_span_singleton (hπ : Irreducible π) {v : M}
    (hv : LinearIndependent R ![v]) :
    HasAtomicDecomposition π (q.comp (Submodule.span R (Set.range ![v])).subtype) := by
  let b := Basis.span hv
  have hy (y : Submodule.span R (Set.range ![v])) : (y : M) = b.equivFun y 0 • v := by
    conv_lhs => rw [← b.sum_equivFun y]
    simp [b, Basis.span_apply]
  by_cases hq : q v = 0
  · exact .of_forall_eq_zero π b fun y ↦ by
      simp [hy y, QuadraticMap.map_smul, hq]
  obtain ⟨m, u, hu⟩ := eq_unit_mul_pow_irreducible hq hπ
  refine .of_isAtomic (Q := QuadraticMap.weightedSumSquares R ![(u : R)])
    (.of_unary (LinearEquiv.funUnique (Fin 1) R R) u.isUnit fun x ↦ ?_) b.equivFun m fun y ↦ ?_
  · simp [QuadraticMap.weightedSumSquares_apply]
    ring
  · simp only [QuadraticMap.comp_apply, Submodule.subtype_apply, hy y, QuadraticMap.map_smul, hu,
      QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_one, smul_eq_mul]
    simp
    ring

/-- `q` splits off a nonzero summand `S`, orthogonal to a complement `S'`, on which it has an
atomic decomposition. -/
private def SplitsOff (π : R) (q : QuadraticForm R M) : Prop :=
  ∃ S S' : Submodule R M, IsCompl S S' ∧ S ≠ ⊥ ∧ (∀ x ∈ S, ∀ y ∈ S', polar q x y = 0) ∧
    HasAtomicDecomposition π (q.comp S.subtype)

/-- A vector `x` with a nonzero self-pairing dividing all its pairings spans a unary block which
splits off `q` orthogonally. -/
private theorem splitsOff_of_apply_self_dvd (hπ : Irreducible π) {x : M}
    (hx : polar q x x ≠ 0) (hdvd : ∀ y, polar q x x ∣ polar q x y) : SplitsOff π q := by
  have hli : LinearIndependent R ![x] :=
    LinearMap.BilinForm.linearIndependent_of_isUnit_det (B := q.polarBilin) (G := !![1])
      (mem_nonZeroDivisors_of_ne_zero hx) (fun i j ↦ by fin_cases i; fin_cases j; simp)
      (by simp)
  have hc : IsCompl (Submodule.span R (Set.range ![x]))
      (LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span R (Set.range ![x]))) := by
    simpa using LinearMap.BilinForm.isCompl_span_singleton_orthogonal_of_dvd q.polarBilin
      (mem_nonZeroDivisors_of_ne_zero hx) (by simpa using hdvd)
  refine ⟨_, _, hc, fun h0 ↦ hli.ne_zero 0 ?_, fun _ ha _ hb ↦ by
    simpa using (LinearMap.BilinForm.mem_orthogonal_iff.mp hb) _ ha,
    hasAtomicDecomposition_span_singleton hπ hli⟩
  exact (Submodule.eq_bot_iff _).mp h0 _ (Submodule.subset_span (Set.mem_range_self 0))

/-- Let `u, w` have a nonzero mutual pairing `β` dividing every value of the polar pairing, with
self-pairings `β s` and `β t` for a nonunit `s`, and let `q u ∣ q w`. When `2` is not a unit,
`u` and `w` span a binary atomic block which splits off `q` orthogonally. -/
private theorem splitsOff_of_apply_pair (hπ : Irreducible π) (h2 : ¬IsUnit (2 : R))
    {u w : M} {s t : R} (hd : polar q u w ≠ 0) (hdvd : ∀ x y, polar q u w ∣ polar q x y)
    (hs : polar q u u = polar q u w * s) (ht : polar q w w = polar q u w * t)
    (hs' : ¬IsUnit s) (huw : q u ∣ q w) : SplitsOff π q := by
  obtain ⟨hli, hmod⟩ := q.isSymm_polarBilin.linearIndependent_and_isModular_restrict_span_pair
    (u := u) (w := w) (mem_nonZeroDivisors_of_ne_zero hd) rfl hs ht
    (fun h ↦ hs' (isUnit_of_mul_isUnit_left h))
  have hc := hmod.isCompl_orthogonal (mem_nonZeroDivisors_of_ne_zero hd) (by simpa using hdvd)
  refine ⟨_, _, hc, fun h0 ↦ hli.ne_zero 0 ?_, fun _ ha _ hb ↦ by
    simpa using (LinearMap.BilinForm.mem_orthogonal_iff.mp hb) _ ha,
    ?_⟩
  · exact (Submodule.eq_bot_iff _).mp h0 _ (Submodule.subset_span (Set.mem_range_self 0))
  -- Normalize the coefficients `[q u, polar q u w, q w]` by their content `g = ε π ^ m`.
  obtain ⟨g, a₀, b₀, hg, ha₀, hb₀, hunit⟩ : ∃ g a₀ b₀ : R,
      g ≠ 0 ∧ q u = g * a₀ ∧ polar q u w = g * b₀ ∧ (IsUnit a₀ ∨ IsUnit b₀) := by
    rcases ValuationRing.dvd_total (q u) (polar q u w) with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨q u, 1, k, fun h0 ↦ hd (by simp [hk, h0]), (mul_one _).symm, hk, .inl isUnit_one⟩
    · exact ⟨polar q u w, k, 1, hd, hk, (mul_one _).symm, .inr isUnit_one⟩
  obtain ⟨k, hk⟩ := huw
  obtain ⟨m, ε, hε⟩ := eq_unit_mul_pow_irreducible hg hπ
  have hb₀0 : b₀ ≠ 0 := fun h0 ↦ hd (by rw [hb₀, h0, mul_zero])
  -- From `2 q u = β s`, after cancelling the content.
  have h2a : 2 * a₀ = b₀ * s := by
    refine mul_left_cancel₀ hg ?_
    have : polar q u u = 2 * q u := by rw [polar_self, nsmul_eq_mul, Nat.cast_ofNat]
    linear_combination -2 * ha₀ - this + hs + s * hb₀
  let b := Basis.span hli
  have hy (y : Submodule.span R (Set.range ![u, w])) :
      (y : M) = b.equivFun y 0 • u + b.equivFun y 1 • w := by
    conv_lhs => rw [← b.sum_equivFun y]
    simp [b, Basis.span_apply, Fin.sum_univ_two]
  refine .of_isAtomic (m := m) (Q := QuadraticMap.weightedSumSquares R ![ε * a₀, ε * (a₀ * k)] +
      (ε * b₀) • QuadraticMap.linMulLin (LinearMap.proj 0) (LinearMap.proj 1))
    (.of_binary h2 (a := ε * a₀) (b := ε * b₀) (c := ε * (a₀ * k)) (LinearEquiv.refl R _)
      ?_ ?_ ?_ fun x ↦ ?_) b.equivFun fun y ↦ ?_
  · -- `v(ε b₀) < v(2 ε a₀) = v(ε b₀ s)` since `s` is not a unit.
    rw [show 2 * (ε * a₀) = ε * b₀ * s by linear_combination (ε : R) * h2a]
    refine lt_of_le_not_ge (addVal_le_iff_dvd.mpr (dvd_mul_right _ _)) fun hle ↦ hs' ?_
    obtain ⟨r, hr⟩ := addVal_le_iff_dvd.mp hle
    refine IsUnit.of_mul_eq_one r (mul_left_cancel₀ (mul_ne_zero ε.ne_zero hb₀0) ?_)
    linear_combination -hr
  · exact addVal_le_iff_dvd.mpr ⟨k, by ring⟩
  · exact hunit.imp ε.isUnit.mul ε.isUnit.mul
  · simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two]
    ring
  · simp only [QuadraticMap.comp_apply, Submodule.subtype_apply, hy y, QuadraticMap.map_add,
      QuadraticMap.map_smul, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
    simp only [Basis.equivFun_apply, smul_eq_mul, add_apply, weightedSumSquares_apply,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      smul_apply, linMulLin_apply, LinearMap.coe_proj, Function.eval]
    rw [hk, ha₀, hb₀, hε]
    ring

/-- If the polar pairing of `q` vanishes, a basis vector spans a unary or a zero block which
splits off `q` orthogonally. -/
private theorem splitsOff_of_forall_polar_eq_zero (hπ : Irreducible π) {k : ℕ}
    (b : Basis (Fin (k + 1)) R M) (hT : ∀ x y, polar q x y = 0) : SplitsOff π q := by
  have hli : LinearIndependent R ![b 0] := by
    convert b.linearIndependent.comp ![0] (Function.injective_of_subsingleton _) using 1
    ext i
    fin_cases i
    rfl
  have hc := b.linearIndependent.isCompl_span_image b.span_eq (isCompl_compl (x := {0}))
  rw [Set.image_singleton, ← Matrix.range_cons_empty (b 0) ![]] at hc
  refine ⟨_, _, hc, fun h0 ↦ hli.ne_zero 0 ?_, fun x _ y _ ↦ hT x y,
    hasAtomicDecomposition_span_singleton hπ hli⟩
  exact (Submodule.eq_bot_iff _).mp h0 _ (Submodule.subset_span (Set.mem_range_self 0))

/-- If the polar pairing of `q` does not vanish, a unary or a binary atomic block splits off `q`
orthogonally. A pairing `β = polar q u w` of basis vectors of minimal valuation divides every
value of the pairing. If some self-pairing is `β` times a unit, its vector spans a unary block;
this happens for `u`, `w` or `u + w` whenever `2` is a unit. Otherwise `u` and `w` span a binary
block. -/
private theorem splitsOff_of_polar_ne_zero [Free R M] [Module.Finite R M] (hπ : Irreducible π)
    {x₀ y₀ : M} (hxy₀ : polar q x₀ y₀ ≠ 0) : SplitsOff π q := by
  let b := Free.chooseBasis R M
  have : Nontrivial M := ⟨⟨x₀, 0, fun h ↦ hxy₀ (by simp [h])⟩⟩
  have : Nonempty (Free.ChooseBasisIndex R M) := b.index_nonempty
  obtain ⟨⟨i₀, j₀⟩, hij⟩ :=
    TauCeti.PreValuationRing.exists_forall_dvd fun p : _ × _ ↦ polar q (b p.1) (b p.2)
  set u := b i₀
  set w := b j₀
  have hdvd : ∀ x y, polar q u w ∣ polar q x y := by
    simpa using LinearMap.BilinForm.dvd_apply_of_forall_dvd_basis (B := q.polarBilin) b
      (d := polar q u w) (fun k l ↦ by simpa using hij (k, l))
  have hd : polar q u w ≠ 0 := fun h0 ↦ hxy₀ (zero_dvd_iff.mp (h0 ▸ hdvd x₀ y₀))
  obtain ⟨s, hs⟩ := hdvd u u
  obtain ⟨t, ht⟩ := hdvd w w
  have unary (x : M) (r : R) (hr : IsUnit r) (hx : polar q x x = polar q u w * r) :
      SplitsOff π q := by
    refine splitsOff_of_apply_self_dvd hπ (by rw [hx]; exact mul_ne_zero hd hr.ne_zero)
      fun y ↦ ?_
    rw [hx, ← hr.unit_spec, Units.mul_right_dvd]
    exact hdvd x y
  by_cases hsu : IsUnit s
  · exact unary u s hsu hs
  by_cases htu : IsUnit t
  · exact unary w t htu ht
  by_cases h2 : IsUnit (2 : R)
  · have hst : ¬IsUnit (s + t) := fun h ↦
      (IsLocalRing.isUnit_or_isUnit_of_isUnit_add h).elim hsu htu
    refine unary (u + w) (s + t + 2) ?_ ?_
    · refine (IsLocalRing.isUnit_or_isUnit_of_isUnit_add (b := -(s + t)) ?_).resolve_right
        (by rwa [IsUnit.neg_iff])
      convert h2 using 1
      ring
    · rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
        QuadraticMap.polar_add_right]
      linear_combination hs + ht + polar_comm q w u
  rcases ValuationRing.dvd_total (q u) (q w) with huw | hwu
  · exact splitsOff_of_apply_pair hπ h2 hd hdvd hs ht hsu huw
  · have hcomm : polar q w u = polar q u w := polar_comm q w u
    exact splitsOff_of_apply_pair hπ h2 (hcomm ▸ hd) (hcomm ▸ hdvd) (hcomm ▸ ht) (hcomm ▸ hs)
      htu hwu

end Split

/-- Every quadratic form on a free module of finite rank over a discrete valuation ring has an
atomic decomposition. -/
private theorem hasAtomicDecomposition (hπ : Irreducible π) (n : ℕ) {M : Type*} [AddCommGroup M]
    [Module R M] [Free R M] [Module.Finite R M] (q : QuadraticForm R M) (hn : finrank R M = n) :
    HasAtomicDecomposition π q := by
  induction n using Nat.strong_induction_on generalizing M with | _ n ih
  -- Splitting off a nonzero summand reduces to its orthogonal complement, of smaller rank.
  have split (h : SplitsOff π q) : HasAtomicDecomposition π q := by
    obtain ⟨S, S', hc, hS, horth, h⟩ := h
    obtain ⟨_, _⟩ := S'.finite_free_of_isCompl hc.symm
    exact .of_isCompl hc horth h
      (ih _ (hn ▸ Submodule.finrank_lt_of_isCompl_of_ne_bot hc hS) _ rfl)
  by_cases hT : ∀ x y, polar q x y = 0
  · obtain _ | k := n
    · have : Subsingleton M := (finBasisOfFinrankEq R M hn).equivFun.toEquiv.subsingleton
      exact .of_forall_eq_zero π (finBasisOfFinrankEq R M hn) fun x ↦ by
        rw [Subsingleton.elim x 0, map_zero]
    exact split (splitsOff_of_forall_polar_eq_zero hπ (finBasisOfFinrankEq R M hn) hT)
  simp only [not_forall] at hT
  obtain ⟨x₀, y₀, hxy₀⟩ := hT
  exact split (splitsOff_of_polar_ne_zero hπ hxy₀)

/-- **Atomic normal form.** Every quadratic form `q` on a finite projective module over a discrete
valuation ring with uniformizer `π`, of any characteristic, is an orthogonal sum
`π^{e₁} Q₁ ⊥ ⋯ ⊥ π^{e_s} Q_s ⊥ 0` of uniformizer powers of atomic forms of rank one or two, with
`e₁ ≤ ⋯ ≤ e_s`, and of a summand of rank `z` on which `q` vanishes. -/
theorem exists_atomic_normal_form [Module.Finite R M] [Module.Projective R M]
    (q : QuadraticForm R M) {π : R} (hπ : Irreducible π) :
    ∃ (s z : ℕ) (size exponent : Fin s → ℕ)
      (blocks : (i : Fin s) → QuadraticForm R (Fin (size i) → R))
      (e : M ≃ₗ[R] ((i : Fin s) → Fin (size i) → R) × (Fin z → R)),
      Monotone exponent ∧ (∀ i, size i = 1 ∨ size i = 2) ∧ (∀ i, (blocks i).IsAtomic) ∧
      ∀ x, q x = ∑ i, π ^ exponent i * blocks i ((e x).1 i) := by
  have : Free R M := free_of_flat_of_isLocalRing
  exact (hasAtomicDecomposition hπ _ q rfl).exists_monotone

end QuadraticMap
