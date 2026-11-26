/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.RingTheory.GradedAlgebra.Basic
import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# The positive part and the indecomposables of a `ℤ`-graded algebra

For an internally `ℤ`-graded algebra `A = ⨁ₚ Aᵖ`, the positive part `A⁺ = ⨁_{p > 0} Aᵖ` and its
module of indecomposables `Q(A) = A⁺ ⧸ A⁺ · A⁺` measure generators: when `A` vanishes in negative
degrees, `A⁺` is a two-sided ideal, and `Q(A)` is the space of elements of positive degree modulo
the decomposable ones, those that are sums of products of two elements of positive degree. For the
free graded-commutative algebra `ΛV` on generators of positive degree, `Q(ΛV)` is spanned by the
classes of the generators, and a Sullivan algebra `(ΛV, d)` is minimal exactly when the map `d`
induces on `Q(ΛV)` vanishes.

In a graded algebra the decomposables `A⁺ · A⁺` form a homogeneous submodule, so `Q(A)` is graded
in turn: its degree-`p` part `Qᵖ(A)` is `Aᵖ` modulo the span of the products `Aⁱ · Aʲ` with
`i, j > 0` and `i + j = p`, and a graded algebra map induces a linear map on each `Qᵖ`. For the
cohomology algebra of a compact Lie group or of an arithmetic group, `Qᵖ` is the space of
primitive classes of degree `p` whose determinant lines Borel compares through invariant forms.

Mathlib's irrelevant ideal `HomogeneousIdeal.irrelevant` is the same construction for gradings by
a canonically ordered monoid such as `ℕ`, and its cotangent space `Ideal.Cotangent` the analogue of
`Q(A)` for commutative rings; here the grading is by `ℤ` and `A` need not be commutative.

## Main definitions

* `TauCeti.positivePart 𝒜`: the submodule `A⁺ = ⨆_{p > 0} Aᵖ`.
* `TauCeti.Indecomposables 𝒜`: the indecomposables `A⁺ ⧸ A⁺ · A⁺`, with the projection
  `TauCeti.Indecomposables.mk`.
* `TauCeti.Indecomposables.map`: the map induced on indecomposables by a linear map carrying
  positive parts and decomposables into positive parts and decomposables.
* `TauCeti.homogeneousDecomposables 𝒜 p`: the decomposables of degree `p`, the span of the
  products `Aⁱ · Aʲ` with `i, j > 0` and `i + j = p`.
* `TauCeti.Indecomposables.homogeneousSubmodule 𝒜 p`: the degree-`p` indecomposables `Qᵖ(A)`,
  the classes of the elements of `A⁺` of degree `p`, and
  `TauCeti.Indecomposables.homogeneousSubmoduleEquiv`: for `p > 0`, the identification of `Qᵖ(A)`
  with `Aᵖ` modulo the decomposables of degree `p`.
* `TauCeti.Indecomposables.homogeneousMap`: the map `Qᵖ(A) → Qᵖ(B)` induced by a graded algebra
  map.

## Main results

* `TauCeti.positivePart_le_iff`: `A⁺` is the least submodule containing every `Aᵖ`, `p > 0`;
  `TauCeti.mem_positivePart_iff`: its elements are those with no component of degree `≤ 0`.
* `TauCeti.map_positivePart_le`, `TauCeti.map_positivePart_mul_positivePart_le`: maps raising
  degrees carry `A⁺` into `B⁺`, and algebra maps carrying `A⁺` into `B⁺` carry `A⁺ · A⁺` into
  `B⁺ · B⁺`, the two hypotheses of `TauCeti.Indecomposables.map`.
* `GradedAlgHom.map_positivePart_le`, `GradedAlgHom.map_positivePart_mul_positivePart_le`: a
  degree-preserving algebra map discharges both hypotheses, so it induces a map on
  indecomposables.
* `TauCeti.mul_mem_positivePart_of_left`, `TauCeti.mul_mem_positivePart_of_right`: when `A`
  vanishes in negative degrees, `A⁺` is a two-sided ideal, and so is `A⁺ · A⁺`
  (`TauCeti.mul_mem_positivePart_mul_positivePart_of_left` and its mirror).
* `TauCeti.Indecomposables.map_id`, `TauCeti.Indecomposables.map_comp`: functoriality of the
  induced maps.
* `TauCeti.Indecomposables.map_eq_zero_iff`: the induced map vanishes exactly when it carries
  `A⁺` into the decomposables.
* `TauCeti.Indecomposables.lift`, `TauCeti.Indecomposables.hom_ext`: the universal property of
  `Q(A)` as a quotient.
* `TauCeti.positivePart_mul_positivePart_eq_iSup`,
  `TauCeti.inf_positivePart_mul_positivePart`: in a graded algebra, `A⁺ · A⁺` is the sum of the
  decomposables of each degree, and its elements of degree `p` are the decomposables of degree
  `p`.
* `TauCeti.Indecomposables.isInternal_homogeneousSubmodule`: `Q(A)` is the internal direct sum
  of the degree-`p` indecomposables `Qᵖ(A)`, which vanish for `p ≤ 0`
  (`TauCeti.Indecomposables.homogeneousSubmodule_eq_bot`).
* `TauCeti.Indecomposables.map_homogeneousSubmodule_le`: a linear map raising degrees by `n`
  carries `Qᵖ(A)` into `Qᵖ⁺ⁿ(B)`; `TauCeti.Indecomposables.homogeneousMap_id` and
  `TauCeti.Indecomposables.homogeneousMap_comp`: functoriality of the maps induced by graded
  algebra maps.

## References

* J. W. Morgan, *The algebraic topology of smooth algebraic varieties*, Publ. Math. IHÉS 48
  (1978), §5, after Definition 5.2.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational homotopy theory*, Graduate Texts in Mathematics
  205, Springer, 2001, §12.
* A. Borel, *Cohomologie de SLₙ et valeurs de fonctions zêta aux points entiers*, Ann. Scuola
  Norm. Sup. Pisa 4 (1977), §1.3, for the indecomposables of a cohomology algebra in each degree.
-/

public section

namespace TauCeti

section Semiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (𝒜 : ℤ → Submodule R A)

/-- The positive part `A⁺ = ⨆_{p > 0} Aᵖ` of an internally `ℤ`-graded algebra: the elements whose
homogeneous components all have positive degree. -/
def positivePart : Submodule R A :=
  ⨆ (p : ℤ) (_ : 0 < p), 𝒜 p

variable {𝒜}

/-- A homogeneous element of positive degree lies in the positive part. -/
theorem mem_positivePart_of_mem {p : ℤ} (hp : 0 < p) {a : A} (ha : a ∈ 𝒜 p) :
    a ∈ positivePart 𝒜 :=
  (le_iSup₂ (f := fun (p : ℤ) (_ : 0 < p) => 𝒜 p) p hp) ha

/-- The positive part is the least submodule containing every homogeneous component of positive
degree. -/
theorem positivePart_le_iff {P : Submodule R A} :
    positivePart 𝒜 ≤ P ↔ ∀ p, 0 < p → 𝒜 p ≤ P :=
  iSup₂_le_iff

/-- A linear map raising degrees by `n ≥ 0` carries the positive part into the positive part. -/
theorem map_positivePart_le {B : Type*} [Semiring B] [Algebra R B] {ℬ : ℤ → Submodule R B}
    {n : ℤ} (hn : 0 ≤ n) {f : A →ₗ[R] B} (hf : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → f a ∈ ℬ (p + n)) :
    (positivePart 𝒜).map f ≤ positivePart ℬ :=
  Submodule.map_le_iff_le_comap.2 <| positivePart_le_iff.2 fun p hp _ ha =>
    mem_positivePart_of_mem (by omega) (hf ha)

/-- An algebra map carrying the positive part into the positive part carries the decomposables
`A⁺ · A⁺` into the decomposables, as needed to induce a map on indecomposables. -/
theorem map_positivePart_mul_positivePart_le {B : Type*} [Semiring B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} {f : A →ₐ[R] B}
    (hf : (positivePart 𝒜).map f.toLinearMap ≤ positivePart ℬ) :
    (positivePart 𝒜 * positivePart 𝒜).map f.toLinearMap ≤ positivePart ℬ * positivePart ℬ := by
  rw [Submodule.map_mul]
  exact mul_le_mul' hf hf

end Semiring

section GradedAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {𝒜 : ℤ → Submodule R A}
  [GradedAlgebra 𝒜]

/-- An element lies in the positive part exactly when its homogeneous components of degree `≤ 0`
vanish. -/
theorem mem_positivePart_iff {a : A} :
    a ∈ positivePart 𝒜 ↔ ∀ p ≤ 0, (DirectSum.decompose 𝒜 a p : A) = 0 := by
  constructor
  · intro ha p hp
    refine positivePart_le_iff (P := LinearMap.ker (GradedAlgebra.proj 𝒜 p)).2
      (fun q hq b hb => ?_) ha
    rw [LinearMap.mem_ker, GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hb (by omega)]
  · intro ha
    classical
    rw [← DirectSum.sum_support_decompose 𝒜 a]
    refine sum_mem fun p _ => ?_
    by_cases hp0 : p ≤ 0
    · rw [ha p hp0]
      exact zero_mem _
    · exact mem_positivePart_of_mem (by omega) (SetLike.coe_mem _)

/-- **The positive part is homogeneous**: every homogeneous component of an element of the
positive part lies in the positive part. -/
theorem decompose_mem_positivePart {a : A} (ha : a ∈ positivePart 𝒜) (p : ℤ) :
    (DirectSum.decompose 𝒜 a p : A) ∈ positivePart 𝒜 := by
  rcases le_or_gt p 0 with hp | hp
  · rw [mem_positivePart_iff.1 ha p hp]
    exact zero_mem _
  · exact mem_positivePart_of_mem hp (SetLike.coe_mem _)

/-- When `A` vanishes in negative degrees, the positive part is a right ideal. -/
theorem mul_mem_positivePart_of_left (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) {a : A}
    (ha : a ∈ positivePart 𝒜) (b : A) : a * b ∈ positivePart 𝒜 := by
  induction b using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q b =>
    obtain ⟨b, hb⟩ := b
    refine positivePart_le_iff (P := (positivePart 𝒜).comap (LinearMap.mulRight R b)).2
      (fun p hp a ha => ?_) ha
    by_cases hq : 0 ≤ q
    · exact mem_positivePart_of_mem (by omega) (SetLike.GradedMul.mul_mem ha hb)
    · simp [(Submodule.eq_bot_iff _).1 (h𝒜 _ (by omega)) b hb]
  | add b b' hb hb' => simpa [mul_add] using add_mem hb hb'

/-- When `A` vanishes in negative degrees, the positive part is a left ideal. -/
theorem mul_mem_positivePart_of_right (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) (a : A) {b : A}
    (hb : b ∈ positivePart 𝒜) : a * b ∈ positivePart 𝒜 := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous p a =>
    obtain ⟨a, ha⟩ := a
    refine positivePart_le_iff (P := (positivePart 𝒜).comap (LinearMap.mulLeft R a)).2
      (fun q hq b hb => ?_) hb
    by_cases hp : 0 ≤ p
    · exact mem_positivePart_of_mem (by omega) (SetLike.GradedMul.mul_mem ha hb)
    · simp [(Submodule.eq_bot_iff _).1 (h𝒜 _ (by omega)) a ha]
  | add a a' ha ha' => simpa [add_mul] using add_mem ha ha'

/-- When `A` vanishes in negative degrees, the decomposables `A⁺ · A⁺` form a right ideal. -/
theorem mul_mem_positivePart_mul_positivePart_of_left (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) {a : A}
    (ha : a ∈ positivePart 𝒜 * positivePart 𝒜) (b : A) :
    a * b ∈ positivePart 𝒜 * positivePart 𝒜 := by
  refine Submodule.mul_induction_on ha (fun a ha a' ha' => ?_) fun a a' ha ha' => ?_
  · rw [mul_assoc]
    exact Submodule.mul_mem_mul ha (mul_mem_positivePart_of_left h𝒜 ha' b)
  · simpa [add_mul] using add_mem ha ha'

/-- When `A` vanishes in negative degrees, the decomposables `A⁺ · A⁺` form a left ideal. -/
theorem mul_mem_positivePart_mul_positivePart_of_right (h𝒜 : ∀ p < 0, 𝒜 p = ⊥) (a : A) {b : A}
    (hb : b ∈ positivePart 𝒜 * positivePart 𝒜) :
    a * b ∈ positivePart 𝒜 * positivePart 𝒜 := by
  refine Submodule.mul_induction_on hb (fun b hb b' hb' => ?_) fun b b' hb hb' => ?_
  · rw [← mul_assoc]
    exact Submodule.mul_mem_mul (mul_mem_positivePart_of_right h𝒜 a hb) hb'
  · simpa [mul_add] using add_mem hb hb'

end GradedAlgebra

section Indecomposables

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (𝒜 : ℤ → Submodule R A)

/-- The module of indecomposables `Q(A) = A⁺ ⧸ A⁺ · A⁺` of an internally `ℤ`-graded algebra: the
elements of positive degree modulo the decomposable ones, the sums of products of two elements of
positive degree. -/
abbrev Indecomposables : Type _ :=
  positivePart 𝒜 ⧸ (positivePart 𝒜 * positivePart 𝒜).comap (positivePart 𝒜).subtype

namespace Indecomposables

/-- The projection `A⁺ → Q(A)` onto the indecomposables. -/
def mk : positivePart 𝒜 →ₗ[R] Indecomposables 𝒜 :=
  Submodule.mkQ _

variable {𝒜}

theorem mk_surjective : Function.Surjective (mk 𝒜) :=
  Submodule.mkQ_surjective _

/-- The projection onto the indecomposables is the quotient map `Submodule.mkQ`. -/
theorem mk_eq_mkQ :
    mk 𝒜 = Submodule.mkQ ((positivePart 𝒜 * positivePart 𝒜).comap (positivePart 𝒜).subtype) :=
  (rfl)

/-- The projection onto the indecomposables is the quotient map. -/
theorem mk_apply (a : positivePart 𝒜) : mk 𝒜 a = Submodule.Quotient.mk a :=
  (rfl)

/-- Two elements of positive degree have the same class in the indecomposables exactly when they
differ by a decomposable element. -/
theorem mk_eq_mk_iff {a b : positivePart 𝒜} :
    mk 𝒜 a = mk 𝒜 b ↔ (a - b : A) ∈ positivePart 𝒜 * positivePart 𝒜 :=
  Submodule.Quotient.eq _

/-- An element of positive degree has zero class in the indecomposables exactly when it is
decomposable. -/
@[simp]
theorem mk_eq_zero_iff {a : positivePart 𝒜} :
    mk 𝒜 a = 0 ↔ (a : A) ∈ positivePart 𝒜 * positivePart 𝒜 :=
  Submodule.Quotient.mk_eq_zero _

variable {B : Type*} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} {f : A →ₗ[R] B}

/-- The map `Q(f) : Q(A) → Q(B)` induced on indecomposables by a linear map `f : A → B` which
carries `A⁺` into `B⁺` and `A⁺ · A⁺` into `B⁺ · B⁺`. -/
def map (f : A →ₗ[R] B) (hf : (positivePart 𝒜).map f ≤ positivePart ℬ)
    (hf' : (positivePart 𝒜 * positivePart 𝒜).map f ≤ positivePart ℬ * positivePart ℬ) :
    Indecomposables 𝒜 →ₗ[R] Indecomposables ℬ :=
  Submodule.mapQ _ _ (f.restrict fun a ha => hf ⟨a, ha, rfl⟩) fun a ha =>
    hf' ⟨a, ha, rfl⟩

@[simp]
theorem map_mk (hf : (positivePart 𝒜).map f ≤ positivePart ℬ)
    (hf' : (positivePart 𝒜 * positivePart 𝒜).map f ≤ positivePart ℬ * positivePart ℬ)
    (a : positivePart 𝒜) :
    map f hf hf' (mk 𝒜 a) = mk ℬ ⟨f a, hf ⟨a, a.property, rfl⟩⟩ :=
  (rfl)

/-- The identity induces the identity on indecomposables. -/
@[simp]
theorem map_id :
    map (LinearMap.id : A →ₗ[R] A) (by simp) (by simp) =
      (LinearMap.id : Indecomposables 𝒜 →ₗ[R] Indecomposables 𝒜) :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

/-- The map induced on indecomposables is functorial: `Q(g ∘ f) = Q(g) ∘ Q(f)`. -/
theorem map_comp {C : Type*} [Ring C] [Algebra R C] {𝒞 : ℤ → Submodule R C} {g : B →ₗ[R] C}
    (hf : (positivePart 𝒜).map f ≤ positivePart ℬ)
    (hf' : (positivePart 𝒜 * positivePart 𝒜).map f ≤ positivePart ℬ * positivePart ℬ)
    (hg : (positivePart ℬ).map g ≤ positivePart 𝒞)
    (hg' : (positivePart ℬ * positivePart ℬ).map g ≤ positivePart 𝒞 * positivePart 𝒞) :
    map (g ∘ₗ f) (Submodule.map_comp f g _ ▸ (Submodule.map_mono hf).trans hg)
        (Submodule.map_comp f g _ ▸ (Submodule.map_mono hf').trans hg') =
      map g hg hg' ∘ₗ map f hf hf' :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

/-- The map induced on indecomposables vanishes exactly when `f` carries `A⁺` into the
decomposables `B⁺ · B⁺`. -/
theorem map_eq_zero_iff (hf : (positivePart 𝒜).map f ≤ positivePart ℬ)
    (hf' : (positivePart 𝒜 * positivePart 𝒜).map f ≤ positivePart ℬ * positivePart ℬ) :
    map f hf hf' = 0 ↔ (positivePart 𝒜).map f ≤ positivePart ℬ * positivePart ℬ := by
  constructor
  · rintro h _ ⟨a, ha, rfl⟩
    have := LinearMap.congr_fun h (mk 𝒜 ⟨a, ha⟩)
    rwa [map_mk, LinearMap.zero_apply, mk_eq_zero_iff] at this
  · intro h
    refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := mk_surjective q
    rw [map_mk, LinearMap.zero_apply, mk_eq_zero_iff]
    exact h ⟨a, a.property, rfl⟩

/-- **The universal property of the indecomposables**: a linear map `g : A → M` vanishing on the
products of two elements of positive degree induces a linear map `Q(A) → M`. -/
def lift {M : Type*} [AddCommGroup M] [Module R M] (g : A →ₗ[R] M)
    (hg : ∀ a ∈ positivePart 𝒜, ∀ b ∈ positivePart 𝒜, g (a * b) = 0) :
    Indecomposables 𝒜 →ₗ[R] M :=
  Submodule.liftQ _ (g ∘ₗ (positivePart 𝒜).subtype) fun a ha =>
    LinearMap.mem_ker.2 <| Submodule.mul_induction_on (C := fun x => g x = 0)
      (Submodule.mem_comap.1 ha) hg fun x y hx hy => by rw [map_add, hx, hy, add_zero]

@[simp]
theorem lift_mk {M : Type*} [AddCommGroup M] [Module R M] (g : A →ₗ[R] M)
    (hg : ∀ a ∈ positivePart 𝒜, ∀ b ∈ positivePart 𝒜, g (a * b) = 0) (a : positivePart 𝒜) :
    lift g hg (mk 𝒜 a) = g a := by
  simp [lift, mk_apply]

/-- Linear maps out of the indecomposables agree when they agree on the classes of the elements of
positive degree: the uniqueness half of the universal property of `lift`. -/
theorem hom_ext {M : Type*} [AddCommGroup M] [Module R M]
    {φ ψ : Indecomposables 𝒜 →ₗ[R] M} (h : ∀ a, φ (mk 𝒜 a) = ψ (mk 𝒜 a)) : φ = ψ :=
  Submodule.linearMap_qext _ (LinearMap.ext h)

end Indecomposables

end Indecomposables

section HomogeneousDecomposables

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (𝒜 : ℤ → Submodule R A)

/-- The decomposables of degree `p`: the span of the products `a * b` of homogeneous elements
`a ∈ Aⁱ` and `b ∈ Aʲ` of positive degrees with `i + j = p`. In a graded algebra these are the
elements of degree `p` of `A⁺ · A⁺` (`TauCeti.inf_positivePart_mul_positivePart`). -/
def homogeneousDecomposables (p : ℤ) : Submodule R A :=
  ⨆ (i : ℤ) (_ : 0 < i) (_ : 0 < p - i), 𝒜 i * 𝒜 (p - i)

variable {𝒜}

/-- A product of homogeneous elements of positive degrees `i` and `j` is decomposable of degree
`i + j`. -/
theorem mul_mem_homogeneousDecomposables {i j : ℤ} (hi : 0 < i) (hj : 0 < j) {a b : A}
    (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) : a * b ∈ homogeneousDecomposables 𝒜 (i + j) := by
  have hb' : b ∈ 𝒜 (i + j - i) := by rwa [add_sub_cancel_left]
  exact (le_iSup₂_of_le i hi (le_iSup_of_le (by omega) le_rfl) :
    𝒜 i * 𝒜 (i + j - i) ≤ homogeneousDecomposables 𝒜 (i + j)) (Submodule.mul_mem_mul ha hb')

/-- The decomposables of degree `p` are the least submodule containing the products of
homogeneous elements of positive degrees adding up to `p`. -/
theorem homogeneousDecomposables_le_iff {p : ℤ} {P : Submodule R A} :
    homogeneousDecomposables 𝒜 p ≤ P ↔
      ∀ i j, 0 < i → 0 < j → i + j = p → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, a * b ∈ P := by
  refine ⟨fun h i j hi hj hij a ha b hb => h (hij ▸ mul_mem_homogeneousDecomposables hi hj ha hb),
    fun h => iSup₂_le fun i hi => iSup_le fun hpi => Submodule.mul_le.2 fun a ha b hb =>
      h i (p - i) hi hpi (by omega) a ha b hb⟩

/-- The decomposables `A⁺ · A⁺` are the sum of the decomposables of each degree. -/
theorem positivePart_mul_positivePart_eq_iSup :
    positivePart 𝒜 * positivePart 𝒜 = ⨆ p, homogeneousDecomposables 𝒜 p := by
  refine le_antisymm (Submodule.mul_le.2 fun a ha b hb => ?_) (iSup_le fun p =>
    homogeneousDecomposables_le_iff.2 fun i j hi hj _ a ha b hb =>
      Submodule.mul_mem_mul (mem_positivePart_of_mem hi ha) (mem_positivePart_of_mem hj hb))
  refine positivePart_le_iff (P := (⨆ p, homogeneousDecomposables 𝒜 p).comap
    (LinearMap.mulRight R b)).2 (fun i hi a ha => ?_) ha
  refine positivePart_le_iff (P := (⨆ p, homogeneousDecomposables 𝒜 p).comap
    (LinearMap.mulLeft R a)).2 (fun j hj b hb => ?_) hb
  exact Submodule.mem_iSup_of_mem (i + j) (mul_mem_homogeneousDecomposables hi hj ha hb)

/-- The decomposables of degree `p` have degree `p`. -/
theorem homogeneousDecomposables_le [SetLike.GradedMul 𝒜] (p : ℤ) :
    homogeneousDecomposables 𝒜 p ≤ 𝒜 p :=
  homogeneousDecomposables_le_iff.2 fun _ _ _ _ hij _ ha _ hb =>
    hij ▸ SetLike.GradedMul.mul_mem ha hb

/-- The decomposables of degree `p` are decomposable. -/
theorem homogeneousDecomposables_le_positivePart_mul_positivePart (p : ℤ) :
    homogeneousDecomposables 𝒜 p ≤ positivePart 𝒜 * positivePart 𝒜 :=
  positivePart_mul_positivePart_eq_iSup (𝒜 := 𝒜) ▸ le_iSup (homogeneousDecomposables 𝒜) p

variable [GradedAlgebra 𝒜]

/-- **The decomposables form a homogeneous submodule**: the degree-`p` component of a decomposable
element is decomposable of degree `p`. -/
theorem decompose_mem_homogeneousDecomposables {a : A}
    (ha : a ∈ positivePart 𝒜 * positivePart 𝒜) (p : ℤ) :
    (DirectSum.decompose 𝒜 a p : A) ∈ homogeneousDecomposables 𝒜 p := by
  rw [positivePart_mul_positivePart_eq_iSup] at ha
  refine Submodule.iSup_induction _ (motive := fun a =>
    (DirectSum.decompose 𝒜 a p : A) ∈ homogeneousDecomposables 𝒜 p) ha (fun q x hx => ?_)
    (by simp) fun x y hx hy => by simpa using add_mem hx hy
  by_cases hqp : q = p
  · subst hqp
    rwa [DirectSum.decompose_of_mem_same 𝒜 (homogeneousDecomposables_le q hx)]
  · rw [DirectSum.decompose_of_mem_ne 𝒜 (homogeneousDecomposables_le q hx) hqp]
    exact zero_mem _

/-- The elements of degree `p` of `A⁺ · A⁺` are the decomposables of degree `p`. -/
theorem inf_positivePart_mul_positivePart (p : ℤ) :
    𝒜 p ⊓ (positivePart 𝒜 * positivePart 𝒜) = homogeneousDecomposables 𝒜 p :=
  le_antisymm (fun a ha => by
      simpa [DirectSum.decompose_of_mem_same 𝒜 ha.1] using
        decompose_mem_homogeneousDecomposables ha.2 p)
    (le_inf (homogeneousDecomposables_le p)
      (homogeneousDecomposables_le_positivePart_mul_positivePart p))

/-- A homogeneous element of degree `p` is decomposable exactly when it lies in the decomposables
of degree `p`. -/
theorem mem_positivePart_mul_positivePart_iff_of_mem {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) :
    a ∈ positivePart 𝒜 * positivePart 𝒜 ↔ a ∈ homogeneousDecomposables 𝒜 p := by
  rw [← inf_positivePart_mul_positivePart, Submodule.mem_inf, and_iff_right ha]

end HomogeneousDecomposables

section HomogeneousSubmodule

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (𝒜 : ℤ → Submodule R A)

namespace Indecomposables

/-- The degree-`p` indecomposables `Qᵖ(A)`: the classes in `Q(A)` of the elements of `A⁺` of
degree `p`. For `p > 0` this is `Aᵖ` modulo the decomposables of degree `p`
(`TauCeti.Indecomposables.homogeneousSubmoduleEquiv`), and for `p ≤ 0` it is zero. -/
def homogeneousSubmodule (p : ℤ) : Submodule R (Indecomposables 𝒜) :=
  ((𝒜 p).comap (positivePart 𝒜).subtype).map (mk 𝒜)

variable {𝒜}

/-- The elements of the degree-`p` indecomposables are the classes of the elements of `A⁺` of
degree `p`. -/
theorem mem_homogeneousSubmodule_iff {p : ℤ} {x : Indecomposables 𝒜} :
    x ∈ homogeneousSubmodule 𝒜 p ↔ ∃ a : positivePart 𝒜, (a : A) ∈ 𝒜 p ∧ mk 𝒜 a = x :=
  Submodule.mem_map

/-- The class of an element of `A⁺` of degree `p` is a degree-`p` indecomposable. -/
theorem mk_mem_homogeneousSubmodule {p : ℤ} {a : positivePart 𝒜} (ha : (a : A) ∈ 𝒜 p) :
    mk 𝒜 a ∈ homogeneousSubmodule 𝒜 p :=
  ⟨a, ha, rfl⟩

/-- A linear map raising degrees by `n` carries the degree-`p` indecomposables into the
degree-`p + n` indecomposables. -/
theorem map_homogeneousSubmodule_le {B : Type*} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B}
    {f : A →ₗ[R] B} (hf : (positivePart 𝒜).map f ≤ positivePart ℬ)
    (hf' : (positivePart 𝒜 * positivePart 𝒜).map f ≤ positivePart ℬ * positivePart ℬ) {n : ℤ}
    (hdeg : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → f a ∈ ℬ (p + n)) (p : ℤ) :
    (homogeneousSubmodule 𝒜 p).map (map f hf hf') ≤ homogeneousSubmodule ℬ (p + n) := by
  rintro _ ⟨_, hx, rfl⟩
  obtain ⟨a, ha, rfl⟩ := mem_homogeneousSubmodule_iff.1 hx
  rw [map_mk]
  exact mk_mem_homogeneousSubmodule (hdeg ha)

/-- For `p > 0`, the degree-`p` indecomposables are the range of the class map `Aᵖ → Q(A)`. -/
theorem homogeneousSubmodule_eq_range {p : ℤ} (hp : 0 < p) :
    homogeneousSubmodule 𝒜 p =
      LinearMap.range (mk 𝒜 ∘ₗ Submodule.inclusion fun _ => mem_positivePart_of_mem hp) := by
  ext x
  rw [mem_homogeneousSubmodule_iff, LinearMap.mem_range]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩, fun ⟨a, h⟩ => ⟨_, a.property, h⟩⟩

variable [GradedAlgebra 𝒜]

variable (𝒜) in
private theorem isHomogeneous_positivePart :
    DirectSum.SetLike.IsHomogeneous (InternalGrading.ofDecomposition 𝒜).piece
      (positivePart 𝒜) := by
  intro p a ha
  simpa using decompose_mem_positivePart ha p

variable (𝒜) in
private theorem isHomogeneous_positivePart_mul_positivePart :
    DirectSum.SetLike.IsHomogeneous ((InternalGrading.ofDecomposition 𝒜).submodule (positivePart 𝒜)
      (isHomogeneous_positivePart 𝒜)).piece
      ((positivePart 𝒜 * positivePart 𝒜).comap (positivePart 𝒜).subtype) := by
  intro p a ha
  simpa using homogeneousDecomposables_le_positivePart_mul_positivePart p
    (decompose_mem_homogeneousDecomposables ha p)

variable (𝒜) in
/-- The grading of `Q(A)` as the quotient of the grading of `A⁺` by its elements of each degree
by the homogeneous submodule `A⁺ · A⁺`; its pieces are the degree-`p` indecomposables. -/
private noncomputable def grading : InternalGrading R (Indecomposables 𝒜) ℤ :=
  ((InternalGrading.ofDecomposition 𝒜).submodule (positivePart 𝒜)
    (isHomogeneous_positivePart 𝒜)).quotient _ (isHomogeneous_positivePart_mul_positivePart 𝒜)

variable (𝒜) in
private theorem grading_piece (p : ℤ) : (grading 𝒜).piece p = homogeneousSubmodule 𝒜 p := by
  simp [grading, homogeneousSubmodule, mk_eq_mkQ]

/-- The indecomposables have no component of degree `p ≤ 0`. -/
theorem homogeneousSubmodule_eq_bot {p : ℤ} (hp : p ≤ 0) : homogeneousSubmodule 𝒜 p = ⊥ := by
  rw [← grading_piece]
  refine InternalGrading.quotient_piece_eq_bot _ _ _ (eq_bot_iff.2 fun a ha => ?_)
  rw [InternalGrading.mem_submodule_piece, InternalGrading.ofDecomposition_piece] at ha
  rw [Submodule.mem_bot, ← Submodule.coe_eq_zero, ← DirectSum.decompose_of_mem_same 𝒜 ha]
  exact mem_positivePart_iff.1 a.property p hp

/-- For `p > 0`, the kernel of the class map `Aᵖ → Q(A)` is the decomposables of degree `p`. -/
theorem ker_mk_comp_inclusion {p : ℤ} (hp : 0 < p) :
    LinearMap.ker (mk 𝒜 ∘ₗ Submodule.inclusion fun _ => mem_positivePart_of_mem hp) =
      (homogeneousDecomposables 𝒜 p).comap (𝒜 p).subtype := by
  ext a
  simp [mem_positivePart_mul_positivePart_iff_of_mem a.property]

/-- **The homogeneous components of the indecomposables**: for `p > 0`, the degree-`p`
indecomposables are `Aᵖ` modulo the span of the products `Aⁱ · Aʲ`, `i, j > 0`, `i + j = p`. -/
noncomputable def homogeneousSubmoduleEquiv {p : ℤ} (hp : 0 < p) :
    (𝒜 p ⧸ (homogeneousDecomposables 𝒜 p).comap (𝒜 p).subtype) ≃ₗ[R]
      homogeneousSubmodule 𝒜 p :=
  (Submodule.quotEquivOfEq _ _ (ker_mk_comp_inclusion hp).symm).trans <|
    (LinearMap.quotKerEquivRange _).trans
      (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_range hp).symm)

@[simp]
theorem homogeneousSubmoduleEquiv_mk {p : ℤ} (hp : 0 < p) (a : 𝒜 p) :
    (homogeneousSubmoduleEquiv hp (Submodule.Quotient.mk a) : Indecomposables 𝒜) =
      mk 𝒜 ⟨a, mem_positivePart_of_mem hp a.property⟩ := by
  simp [homogeneousSubmoduleEquiv, Submodule.inclusion_apply]

@[simp]
theorem homogeneousSubmoduleEquiv_symm_mk {p : ℤ} (hp : 0 < p) (a : 𝒜 p) :
    (homogeneousSubmoduleEquiv hp).symm ⟨mk 𝒜 ⟨a, mem_positivePart_of_mem hp a.property⟩,
      mk_mem_homogeneousSubmodule a.property⟩ = Submodule.Quotient.mk a := by
  rw [LinearEquiv.symm_apply_eq]
  exact Subtype.ext (homogeneousSubmoduleEquiv_mk hp a).symm

/-- **The grading of the indecomposables**: `Q(A)` is the internal direct sum of its homogeneous
components `Qᵖ(A)`. -/
theorem isInternal_homogeneousSubmodule :
    DirectSum.IsInternal (homogeneousSubmodule 𝒜) :=
  funext (grading_piece 𝒜) ▸ (grading 𝒜).isInternal

end Indecomposables

end HomogeneousSubmodule

end TauCeti

namespace GradedAlgHom

open TauCeti

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- A degree-preserving algebra map carries the positive part into the positive part. -/
theorem map_positivePart_le (f : 𝒜 →ₐᵍ[R] ℬ) :
    (positivePart 𝒜).map (f : A →ₐ[R] B).toLinearMap ≤ positivePart ℬ :=
  TauCeti.map_positivePart_le le_rfl fun ha => by
    simpa using Graded.map_mem f ha

/-- A degree-preserving algebra map carries the decomposables `A⁺ · A⁺` into the decomposables
`B⁺ · B⁺`. With `GradedAlgHom.map_positivePart_le` it discharges the hypotheses of
`TauCeti.Indecomposables.map`, so it induces a map on indecomposables. -/
theorem map_positivePart_mul_positivePart_le (f : 𝒜 →ₐᵍ[R] ℬ) :
    (positivePart 𝒜 * positivePart 𝒜).map (f : A →ₐ[R] B).toLinearMap ≤
      positivePart ℬ * positivePart ℬ :=
  TauCeti.map_positivePart_mul_positivePart_le f.map_positivePart_le

end GradedAlgHom

namespace TauCeti.Indecomposables

variable {R A B C : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Ring C]
  [Algebra R C] {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]

/-- The map `Qᵖ(A) → Qᵖ(B)` induced on the degree-`p` indecomposables by a graded algebra map. -/
def homogeneousMap (f : 𝒜 →ₐᵍ[R] ℬ) (p : ℤ) :
    homogeneousSubmodule 𝒜 p →ₗ[R] homogeneousSubmodule ℬ p :=
  (map (f : A →ₐ[R] B).toLinearMap f.map_positivePart_le
      f.map_positivePart_mul_positivePart_le).restrict fun x hx => by
    simpa using map_homogeneousSubmodule_le f.map_positivePart_le
      f.map_positivePart_mul_positivePart_le (n := 0)
      (fun ha => by simpa using Graded.map_mem f ha) p
      ⟨x, hx, rfl⟩

@[simp]
theorem homogeneousMap_mk (f : 𝒜 →ₐᵍ[R] ℬ) {p : ℤ} {a : positivePart 𝒜} (ha : (a : A) ∈ 𝒜 p) :
    (homogeneousMap f p ⟨mk 𝒜 a, mk_mem_homogeneousSubmodule ha⟩ : Indecomposables ℬ) =
      mk ℬ ⟨f a, f.map_positivePart_le ⟨a, a.property, rfl⟩⟩ := by
  simp [homogeneousMap]

/-- The map induced on the degree-`p` indecomposables is the restriction of the map induced on
all indecomposables. -/
theorem coe_homogeneousMap (f : 𝒜 →ₐᵍ[R] ℬ) (p : ℤ) (x : homogeneousSubmodule 𝒜 p) :
    (homogeneousMap f p x : Indecomposables ℬ) =
      map (f : A →ₐ[R] B).toLinearMap f.map_positivePart_le
        f.map_positivePart_mul_positivePart_le x :=
  LinearMap.coe_restrict_apply _ x

/-- The identity induces the identity on the degree-`p` indecomposables. -/
@[simp]
theorem homogeneousMap_id (p : ℤ) :
    homogeneousMap (GradedAlgHom.id R 𝒜) p = LinearMap.id := by
  ext x
  simp [coe_homogeneousMap]

/-- The maps induced on the degree-`p` indecomposables are functorial. -/
theorem homogeneousMap_comp (g : ℬ →ₐᵍ[R] 𝒞) (f : 𝒜 →ₐᵍ[R] ℬ) (p : ℤ) :
    homogeneousMap (g.comp f) p = homogeneousMap g p ∘ₗ homogeneousMap f p := by
  ext x
  simp [coe_homogeneousMap, GradedAlgHom.comp_toAlgHom,
    map_comp f.map_positivePart_le f.map_positivePart_mul_positivePart_le g.map_positivePart_le
      g.map_positivePart_mul_positivePart_le]

end TauCeti.Indecomposables
