/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.DifferentialOperator
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Nat.Choose.Cast

/-!
# The principal symbol of a differential operator by iterated commutators

Let `A` be a commutative `R`-algebra and `D : M →ₗ[R] N` a differential operator of order at
most `m` between `A`-modules, in Grothendieck's sense (`TauCeti.differentialOperators`). For
`a₁, …, aₘ : A` the iterated commutator `[⋯[D, a₁], …, aₘ]` is `A`-linear. As a function of the
`aᵢ` it is symmetric, additive, and a derivation in each slot, and for `m ≥ 1` it vanishes
identically exactly when `D` has order at most `m - 1`. Classically, for the smooth functions on
a manifold acting on smooth sections of vector bundles, its value at `a₁ = ⋯ = aₘ = f` is `m!`
times the principal symbol of `D` evaluated at the covector `df`, so the multilinear map is `m!`
times the polarization of the principal symbol.

The derivation property shows that the value modulo an ideal `I` depends only on the classes
of the `aᵢ ∈ I` in the algebraic cotangent module `I / I²`. For the vanishing ideal `I_x` of a
point `x` of a manifold, this module is the cotangent space `T_x*M`
(`TauCeti.smoothCotangentEquiv`), and `M / I_x M` is the fibre of a bundle at `x` when `M` is its
module of smooth sections. The descended map is then `m!` times the polarized principal symbol
at `x`, a symmetric multilinear map `T_x*M × ⋯ × T_x*M → Hom(E_x, F_x)`.

## Main definitions

* `TauCeti.commutatorSymbol`: the iterated commutator of an operator of order at most `m`, as an
  `R`-multilinear map `Aᵐ → (M →ₗ[A] N)`, `R`-linear in the operator.
* `TauCeti.commutatorSymbolDerivation`: the commutator symbol as a derivation in one slot.
* `TauCeti.cotangentSymbol`: its descent to an `A ⧸ I`-multilinear map
  `(I / I²)ᵐ → (M / I M →ₗ[A ⧸ I] N / I N)`.
* `TauCeti.pointCommutatorSymbol`, `TauCeti.pointPrincipalSymbol`: for an operator on `A`, a
  `𝕜`-point `φ : A →ₐ[𝕜] 𝕜` whose kernel contains `J`, and `e : J / J² ≃ V`, the `𝕜`-multilinear
  form on `V` sending `(e [a₁], …, e [aₘ])` to `φ([⋯[D, a₁], …, aₘ] 1)`, and the homogeneous
  function `v ↦ (1 / m!) σ(v, …, v)`. For the smooth functions on a manifold and evaluation at a
  point, these are the commutator and principal symbols at that point.

## Main results

* `TauCeti.commutatorSymbol_apply_apply`: the commutator symbol is the iterated commutator.
* `TauCeti.commutatorSymbol_eq_zero_iff`: the commutator symbol of an operator of order at most
  `m + 1` vanishes if and only if the operator has order at most `m`.
* `TauCeti.commutatorSymbol_comp_perm`: the commutator symbol is symmetric.
* `TauCeti.commutatorSymbol_update_mul`: the Leibniz rule in each slot.
* `TauCeti.commutatorSymbol_add_algebraMap`: adding scalars to the entries does not change the
  commutator symbol.
* `AlgEquiv.commutatorSymbol_conjDifferentialOperators`: the commutator symbol is natural under
  conjugation by algebra isomorphisms.
* `TauCeti.commutatorSymbol_comp_const`: on the diagonal, commutator symbols multiply under
  composition, up to the binomial coefficient `(m + k).choose m`.
* `Derivation.commutatorSymbol_derivation`: the commutator symbol of a derivation `δ` at `f` is
  multiplication by `δ f`.
* `TauCeti.cotangentSymbol_toCotangent`: the cotangent symbol on classes of elements of `I`;
  `TauCeti.cotangentSymbol_comp_perm` and `TauCeti.cotangentSymbol_comp_const` give its symmetry
  and its composition law.
* `TauCeti.pointCommutatorSymbol_toCotangent`, `TauCeti.pointCommutatorSymbol_comp_perm`,
  `TauCeti.pointPrincipalSymbol_smul_covector`, `TauCeti.pointPrincipalSymbol_comp`: the point
  commutator symbol on classes of elements of `J`, its symmetry, the homogeneity of the point
  principal symbol, and its multiplicativity under composition.
* `Polynomial.commutatorSymbol_derivative_comp_derivative`: for `∂²` on `R[X]` the commutator
  symbol at `(X, X)` is multiplication by `2`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §12.
-/

public section

open Function

namespace TauCeti

section CommSemiring

variable (R : Type*) {A M N O : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]
  [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
  [AddCommGroup O] [Module A O] [Module R O] [IsScalarTower R A O]

variable {R}

/-! ### The commutator symbol -/

/-- An operator of order at most `0`, as an `A`-linear map. -/
private def toLinearMapOfOrderZero : differentialOperators R A M N 0 →ₗ[R] M →ₗ[A] N where
  toFun D :=
    { toFun := D.1
      map_add' := map_add D.1
      map_smul' := mem_differentialOperators_zero_iff.1 D.2 }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The commutator with `a`, from operators of order at most `m + 1` to order at most `m`, as a
bilinear map in the operator and `a`. -/
private def smulCommutatorOfOrderSucc {m : ℕ} :
    differentialOperators R A M N (m + 1) →ₗ[R] A →ₗ[R] differentialOperators R A M N m :=
  LinearMap.mk₂ R (fun D a ↦ ⟨smulCommutator R a D, smulCommutator_mem_differentialOperators D.2 a⟩)
    (fun D E a ↦ by ext; simp) (fun r D a ↦ by ext; simp)
    (fun D a b ↦ by ext; simp [smulCommutator_add]) (fun r D a ↦ by ext; simp [smulCommutator_smul])

variable (R A M N) in
/-- The commutator symbol of a differential operator `D` of order at most `m`: the `R`-multilinear
map sending `(a₁, …, aₘ)` to the `A`-linear iterated commutator `[⋯[D, a₁], …, aₘ]`
(`commutatorSymbol_apply_apply`). It depends `R`-linearly on `D`. For the smooth functions on a
manifold acting on smooth sections of vector bundles, its value at `a₁ = ⋯ = aₘ = f` is `m!`
times the principal symbol of `D` at `df`. -/
def commutatorSymbol : (m : ℕ) →
    differentialOperators R A M N m →ₗ[R] MultilinearMap (RingHom.id R) (fun _ : Fin m ↦ A) (M
        →ₗ[A] N)
  | 0 => (MultilinearMap.constLinearEquivOfIsEmpty R (RingHom.id R) (fun _ : Fin 0 ↦ A)
      (M →ₗ[A] N)).toLinearMap ∘ₗ toLinearMapOfOrderZero
  | m + 1 => (multilinearCurryLeftEquiv (RingHom.id R) (fun _ : Fin (m + 1) ↦ A) (M →ₗ[A]
      N)).symm.toLinearMap ∘ₗ
      LinearMap.compRight R (commutatorSymbol m) ∘ₗ smulCommutatorOfOrderSucc

theorem commutatorSymbol_zero_apply (D : differentialOperators R A M N 0) (a : Fin 0 → A)
    (x : M) : commutatorSymbol R A M N 0 D a x = (D : M →ₗ[R] N) x :=
  (rfl)

/-- The commutator symbol in `m + 1` slots: the commutator with the first entry, followed by the
commutator symbol of the result in the remaining slots. -/
theorem commutatorSymbol_succ_apply {m : ℕ} (D : differentialOperators R A M N (m + 1))
    (a : Fin (m + 1) → A) :
    commutatorSymbol R A M N (m + 1) D a =
      commutatorSymbol R A M N m
        ⟨smulCommutator R (a 0) D, smulCommutator_mem_differentialOperators D.2 _⟩
        (Fin.tail a) :=
  (rfl)

/-- The commutator symbol is the iterated commutator. -/
@[simp]
theorem commutatorSymbol_apply_apply {m : ℕ} (D : differentialOperators R A M N m)
    (a : Fin m → A) (x : M) :
    commutatorSymbol R A M N m D a x =
      (List.ofFn fun i ↦ smulCommutator R (a i)).prod (D : M →ₗ[R] N) x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [commutatorSymbol_succ_apply, ih, List.ofFn_succ, List.prod_cons,
      (commute_smulCommutator_list_prod _ _).eq, mul_apply_eq_comp]
    rfl

/-- The commutator symbol of an operator of order at most `0` is the operator itself. -/
theorem commutatorSymbol_zero_injective :
    Injective (commutatorSymbol R A M N 0) := by
  intro D E h
  ext x
  simpa using congr($h Fin.elim0 x)

/-- The commutator symbol of an operator of order at most `m + 1` vanishes if and only if the
operator has order at most `m`. -/
theorem commutatorSymbol_eq_zero_iff {m : ℕ} (D : differentialOperators R A M N (m + 1)) :
    commutatorSymbol R A M N (m + 1) D = 0 ↔
      (D : M →ₗ[R] N) ∈ differentialOperators R A M N m := by
  rw [mem_differentialOperators_iff_forall_list_prod, MultilinearMap.ext_iff]
  refine forall_congr' fun a ↦ ?_
  simp [LinearMap.ext_iff]

/-- The kernel of the commutator symbol on operators of order at most `m + 1` consists of the
operators of order at most `m`. -/
theorem ker_commutatorSymbol (m : ℕ) :
    LinearMap.ker (commutatorSymbol R A M N (m + 1)) =
      (differentialOperators R A M N m).comap (differentialOperators R A M N (m + 1)).subtype := by
  ext D
  simp [commutatorSymbol_eq_zero_iff]

/-- The commutator symbol is symmetric. -/
theorem commutatorSymbol_comp_perm {m : ℕ} (D : differentialOperators R A M N m)
    (a : Fin m → A) (σ : Equiv.Perm (Fin m)) :
    commutatorSymbol R A M N m D (a ∘ σ) = commutatorSymbol R A M N m D a := by
  ext x
  simp only [commutatorSymbol_apply_apply]
  congr 2
  refine List.Perm.prod_eq' (σ.ofFn_comp_perm fun i ↦ smulCommutator R (a i)) ?_
  exact List.pairwise_ofFn.2 fun _ _ _ ↦ commute_smulCommutator _ _

/-- Multiplying the values of `D` by `g : A` multiplies its commutator symbol by `g`. -/
theorem commutatorSymbol_mk_smul {m : ℕ} (D : differentialOperators R A M N m) (g : A) :
    commutatorSymbol R A M N m ⟨g • (D : M →ₗ[R] N), smul_mem_differentialOperators g D.2⟩ =
      g • commutatorSymbol R A M N m D := by
  ext a x
  simp [list_prod_smulCommutator_apply_smul]

/-- The Leibniz rule in the first slot. -/
theorem commutatorSymbol_cons_mul {m : ℕ} (D : differentialOperators R A M N (m + 1))
    (f g : A) (a : Fin m → A) :
    commutatorSymbol R A M N (m + 1) D (Fin.cons (f * g) a) =
      f • commutatorSymbol R A M N (m + 1) D (Fin.cons g a) +
        g • commutatorSymbol R A M N (m + 1) D (Fin.cons f a) := by
  set P := (List.ofFn fun i ↦ (smulCommutator R (a i) : Module.End R (M →ₗ[R] N))).prod
  have hcons (b : A) :
      (List.ofFn fun i ↦ smulCommutator R ((Fin.cons b a : Fin (m + 1) → A) i)).prod =
        P * smulCommutator R b := by
    rw [List.ofFn_succ, List.prod_cons, (commute_smulCommutator_list_prod _ _).eq]
    simp [P]
  -- The `(m + 2)`-fold commutator `P [[D, f], g]` of an operator of order `m + 1` vanishes.
  have hPD : P (D : M →ₗ[R] N) ∈ differentialOperators R A M N 1 :=
    list_prod_smulCommutator_mem_differentialOperators (by rw [add_comm]; exact D.2) a
  have h0 : P (smulCommutator R g (smulCommutator R f (D : M →ₗ[R] N))) = 0 := by
    rw [← mul_apply_eq_comp P, ← (commute_smulCommutator_list_prod g a).eq, mul_apply_eq_comp,
      ← mul_apply_eq_comp P, ← (commute_smulCommutator_list_prod f a).eq, mul_apply_eq_comp,
      smulCommutator_eq_zero_of_mem_differentialOperators_zero
        (smulCommutator_mem_differentialOperators hPD f) g]
  have hP (c : A) (E : M →ₗ[R] N) : P (c • E) = c • P E := list_prod_smulCommutator_apply_smul a c E
  ext x
  simp only [commutatorSymbol_apply_apply, hcons, mul_apply_eq_comp, smulCommutator_mul, map_add,
    hP, h0, add_zero, LinearMap.add_apply, LinearMap.smul_apply]

/-- The Leibniz rule in each slot: the commutator symbol is a derivation in each entry. -/
theorem commutatorSymbol_update_mul {m : ℕ} (D : differentialOperators R A M N m)
    (a : Fin m → A) (i : Fin m) (f g : A) :
    commutatorSymbol R A M N m D (update a i (f * g)) =
      f • commutatorSymbol R A M N m D (update a i g) +
        g • commutatorSymbol R A M N m D (update a i f) := by
  rcases m with _ | m
  · exact i.elim0
  -- Move the slot `i` to the front by the transposition of `0` and `i`.
  have key (h : A) : commutatorSymbol R A M N (m + 1) D (update a i h) =
      commutatorSymbol R A M N (m + 1) D (Fin.cons h (Fin.tail (a ∘ Equiv.swap 0 i))) := by
    rw [← commutatorSymbol_comp_perm D _ (Equiv.swap 0 i), update_comp_equiv,
      Equiv.symm_swap, Equiv.swap_apply_right, ← Fin.update_cons_zero ((a ∘ Equiv.swap 0 i) 0),
      Fin.cons_self_tail]
  rw [key, key, key, commutatorSymbol_cons_mul]

@[simp]
theorem commutatorSymbol_update_algebraMap {m : ℕ} (D : differentialOperators R A M N m)
    (a : Fin m → A) (i : Fin m) (r : R) :
    commutatorSymbol R A M N m D (update a i (algebraMap R A r)) = 0 := by
  rcases m with _ | m
  · exact i.elim0
  rw [← commutatorSymbol_comp_perm D _ (Equiv.swap 0 i)]
  ext x
  simp [List.ofFn_succ]

/-- Adding scalars to the entries does not change the commutator symbol: the commutator with
multiplication by a scalar vanishes. -/
@[simp]
theorem commutatorSymbol_add_algebraMap {m : ℕ} (D : differentialOperators R A M N m)
    (a : Fin m → A) (r : Fin m → R) :
    commutatorSymbol R A M N m D (fun i ↦ a i + algebraMap R A (r i)) =
      commutatorSymbol R A M N m D a := by
  ext x
  simp [smulCommutator_add]

/-- The commutator symbol, as a derivation in the slot `i` with the other entries of `a` fixed. -/
def commutatorSymbolDerivation {m : ℕ} (D : differentialOperators R A M N m) (a : Fin m → A)
    (i : Fin m) : Derivation R A (M →ₗ[A] N) :=
  Derivation.mk' ((commutatorSymbol R A M N m D).toLinearMap a i) fun f g ↦ by
    simpa using commutatorSymbol_update_mul D a i f g

@[simp]
theorem commutatorSymbolDerivation_apply {m : ℕ} (D : differentialOperators R A M N m)
    (a : Fin m → A) (i : Fin m) (f : A) :
    commutatorSymbolDerivation D a i f = commutatorSymbol R A M N m D (update a i f) := by
  simp [commutatorSymbolDerivation]

/-- On the diagonal, the commutator symbol is the `m`-th power of the commutator with `f`. -/
theorem commutatorSymbol_const_apply {m : ℕ} (D : differentialOperators R A M N m) (f : A)
    (x : M) :
    commutatorSymbol R A M N m D (fun _ ↦ f) x = (smulCommutator R f ^ m) (D : M →ₗ[R] N) x := by
  simp

/-- Composition multiplies commutator symbols on the diagonal: for `P` of order at most `m` and
`Q` of order at most `k`, the commutator symbol of `P ∘ Q` at `f` is `(m + k).choose m` times the
composition of the commutator symbols at `f`. When `(m + k)!` is invertible in `A`, dividing by
factorials shows that principal symbols multiply. -/
theorem commutatorSymbol_comp_const {m k : ℕ} (P : differentialOperators R A N O m)
    (Q : differentialOperators R A M N k) (f : A) :
    commutatorSymbol R A M O (m + k)
        ⟨(P : N →ₗ[R] O) ∘ₗ (Q : M →ₗ[R] N), comp_mem_differentialOperators P.2 Q.2⟩
        (fun _ ↦ f) =
      (m + k).choose m •
        (commutatorSymbol R A N O m P fun _ ↦ f) ∘ₗ (commutatorSymbol R A M N k Q fun _ ↦ f) := by
  ext x
  simp only [commutatorSymbol_const_apply, smulCommutator_pow_comp_of_mem P.2 Q.2,
    LinearMap.smul_apply, LinearMap.comp_apply]

/-- The commutator symbol of an operator `D : A →ₗ[R] M` of order at most one at `f` is
multiplication by `D f - f • D 1`, the value at `f` of the derivation part of `D`. -/
theorem commutatorSymbol_one_apply (D : differentialOperators R A A N 1) (f g : A) :
    commutatorSymbol R A A N 1 D ![f] g =
      g • ((D : A →ₗ[R] N) f - f • (D : A →ₗ[R] N) 1) := by
  have h := congr($(smulCommutator_eq_zero_of_mem_differentialOperators_zero
    (smulCommutator_mem_differentialOperators D.2 f) g) 1)
  simp only [smulCommutator_apply_apply, smul_eq_mul, mul_one, LinearMap.zero_apply] at h
  simp only [commutatorSymbol_apply_apply, List.ofFn_succ, Matrix.cons_val_zero,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, smulCommutator_apply_apply,
    smul_eq_mul, smul_sub]
  rw [sub_eq_zero, sub_eq_iff_eq_add] at h
  rw [h, smul_sub]
  abel

/-- The commutator symbol of a derivation `δ` at `f` is multiplication by `δ f`. -/
theorem _root_.Derivation.commutatorSymbol_derivation (δ : Derivation R A N) (f g : A) :
    commutatorSymbol R A A N 1 ⟨δ, δ.mem_differentialOperators_one⟩ ![f] g = g • δ f := by
  rw [commutatorSymbol_one_apply]
  simp

end CommSemiring

/-! ### Transport along algebra isomorphisms -/

section Conj

variable {R A B : Type*} [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (e : A ≃ₐ[R] B)

/-- The commutator symbol of the conjugate `e ∘ D ∘ e⁻¹` of `D` by an algebra isomorphism `e`, at
the images `e aᵢ`, is the conjugate of the commutator symbol of `D` at the `aᵢ`. -/
theorem _root_.AlgEquiv.commutatorSymbol_conjDifferentialOperators {m : ℕ}
    (D : differentialOperators R A A A m) (a : Fin m → A) (y : B) :
    commutatorSymbol R B B B m (e.conjDifferentialOperators m D) (fun i ↦ e (a i)) y =
      e (commutatorSymbol R A A A m D a (e.symm y)) := by
  rw [commutatorSymbol_apply_apply, AlgEquiv.coe_conjDifferentialOperators,
    e.list_prod_smulCommutator_conj, commutatorSymbol_apply_apply]
  rfl

end Conj

/-! ### Descent to the cotangent module of an ideal -/

section Cotangent

variable {R : Type*} {A M N O : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
  [AddCommGroup O] [Module A O] [Module R O] [IsScalarTower R A O]
  {I : Ideal A}

/-- Modulo `I`, the commutator symbol vanishes when one entry lies in `I ^ 2`. -/
theorem commutatorSymbol_update_apply_mem_smul_top {m : ℕ} (D : differentialOperators R A M N m)
    (a : Fin m → A) (i : Fin m) {c : A} (hc : c ∈ I ^ 2) (x : M) :
    commutatorSymbol R A M N m D (update a i c) x ∈ I • (⊤ : Submodule A N) := by
  rw [pow_two] at hc
  refine Submodule.mul_induction_on
    (C := fun c ↦ commutatorSymbol R A M N m D (update a i c) x ∈ I • (⊤ : Submodule A N)) hc
    (fun f hf g hg ↦ ?_) fun y z hy hz ↦ ?_
  · rw [commutatorSymbol_update_mul]
    exact add_mem (Submodule.smul_mem_smul hf Submodule.mem_top)
      (Submodule.smul_mem_smul hg Submodule.mem_top)
  · simp only [MultilinearMap.map_update_add, LinearMap.add_apply]
    exact add_mem hy hz

/-- Modulo `I`, the commutator symbol depends only on its entries modulo `I ^ 2`. -/
theorem commutatorSymbol_apply_sub_mem_smul_top {m : ℕ} (D : differentialOperators R A M N m)
    {a b : Fin m → A} (h : ∀ i, a i - b i ∈ I ^ 2) (x : M) :
    commutatorSymbol R A M N m D a x - commutatorSymbol R A M N m D b x ∈
      I • (⊤ : Submodule A N) := by
  -- Telescope from `b` to `a` one slot at a time.
  have h' := (commutatorSymbol R A M N m D).map_sub_map_piecewise a b Finset.univ
  rw [Finset.piecewise_univ] at h'
  rw [← LinearMap.sub_apply, h', LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  convert commutatorSymbol_update_apply_mem_smul_top D (fun j ↦ if j < i then a j else b j) i
    (h i) x using 3
  ext j
  rcases lt_trichotomy j i with hj | rfl | hj
  · simp [hj, hj.ne]
  · simp
  · simp [hj.not_gt, hj.ne, hj.ne']

variable (I) in
/-- A representative in `I` of a cotangent class. -/
private noncomputable def cotangentRep (ω : I.Cotangent) : I :=
  surjInv I.toCotangent_surjective ω

private theorem toCotangent_cotangentRep (ω : I.Cotangent) :
    I.toCotangent (cotangentRep I ω) = ω :=
  surjInv_eq I.toCotangent_surjective ω

/-- The commutator symbol reduced modulo `I` at representatives `a` of cotangent classes
does not depend on the representatives. -/
private theorem reduceModIdeal_commutatorSymbol_eq {m : ℕ} (D : differentialOperators R A M N m)
    {a b : Fin m → A} (h : ∀ i, a i - b i ∈ I ^ 2) :
    LinearMap.reduceModIdeal I (commutatorSymbol R A M N m D a) =
      LinearMap.reduceModIdeal I (commutatorSymbol R A M N m D b) := by
  refine LinearMap.ext fun q ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [LinearMap.reduceModIdeal_apply, LinearMap.reduceModIdeal_apply]
  exact (Submodule.Quotient.eq _).2 (commutatorSymbol_apply_sub_mem_smul_top D h x)

/-- Changing one cotangent class to the class of `z ∈ I` amounts, modulo `I`, to changing
the corresponding representative to `z`. -/
private theorem reduceModIdeal_commutatorSymbol_update {m : ℕ}
    (D : differentialOperators R A M N m) (ω : Fin m → I.Cotangent) (i : Fin m) (z : I) :
    LinearMap.reduceModIdeal I (commutatorSymbol R A M N m D
        fun j ↦ (cotangentRep I (update ω i (I.toCotangent z) j) : A)) =
      LinearMap.reduceModIdeal I (commutatorSymbol R A M N m D
        (update (fun j ↦ (cotangentRep I (ω j) : A)) i z)) := by
  refine reduceModIdeal_commutatorSymbol_eq D fun j ↦ ?_
  rcases eq_or_ne j i with rfl | hj
  · simp only [update_self]
    exact I.toCotangent_eq.1 (toCotangent_cotangentRep _)
  · simp only [update_of_ne hj, sub_self, zero_mem]

variable (R I) in
/-- The commutator symbol of `D`, descended to the cotangent module `I / I²` of an ideal `I`:
the `A ⧸ I`-multilinear map sending the classes of `a₁, …, aₘ ∈ I` to the reduction modulo `I` of
the iterated commutator `[⋯[D, a₁], …, aₘ]` (`cotangentSymbol_toCotangent`). For the vanishing
ideal of a point `x` of a manifold, `I / I²` is the cotangent space at `x` and the reductions of
spaces of sections are their fibres at `x`. -/
noncomputable def cotangentSymbol {m : ℕ} (D : differentialOperators R A M N m) :
    MultilinearMap (RingHom.id (A ⧸ I)) (fun _ : Fin m ↦ I.Cotangent)
      ((M ⧸ (I • ⊤ : Submodule A M)) →ₗ[A ⧸ I] (N ⧸ (I • ⊤ : Submodule A N))) where
  toFun ω := LinearMap.reduceModIdeal I
    (commutatorSymbol R A M N m D fun i ↦ (cotangentRep I (ω i) : A))
  map_update_add' ω i u v := by
    obtain rfl : ‹DecidableEq (Fin m)› = instDecidableEqFin m := Subsingleton.elim _ _
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective u
    obtain ⟨z, rfl⟩ := I.toCotangent_surjective v
    rw [← map_add I.toCotangent y z, reduceModIdeal_commutatorSymbol_update,
      reduceModIdeal_commutatorSymbol_update, reduceModIdeal_commutatorSymbol_update,
      Submodule.coe_add, MultilinearMap.map_update_add, map_add]
  map_update_smul' ω i c u := by
    obtain rfl : ‹DecidableEq (Fin m)› = instDecidableEqFin m := Subsingleton.elim _ _
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective u
    rw [show Ideal.Quotient.mk I c • I.toCotangent y = c • I.toCotangent y from
        algebraMap_smul (A ⧸ I) c _, ← map_smul I.toCotangent c y,
      reduceModIdeal_commutatorSymbol_update, reduceModIdeal_commutatorSymbol_update,
      Submodule.coe_smul, smul_eq_mul, commutatorSymbol_update_mul, map_add]
    -- The second Leibniz term is a multiple of `y ∈ I`, so it vanishes modulo `I`.
    refine LinearMap.ext fun q ↦ ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have h0 (v : N) : (y : A) • Submodule.Quotient.mk (p := (I • ⊤ : Submodule A N)) v = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul y.2 Submodule.mem_top
    simp [h0]

/-- The cotangent symbol on the classes of `a₁, …, aₘ ∈ I` is the reduction of the iterated
commutator `[⋯[D, a₁], …, aₘ]` modulo `I`. -/
@[simp]
theorem cotangentSymbol_toCotangent {m : ℕ} (D : differentialOperators R A M N m)
    (a : Fin m → I) (x : M) :
    cotangentSymbol R I D (fun i ↦ I.toCotangent (a i))
        (Submodule.Quotient.mk (p := (I • ⊤ : Submodule A M)) x) =
      Submodule.Quotient.mk (p := (I • ⊤ : Submodule A N))
        (commutatorSymbol R A M N m D (fun i ↦ a i) x) := by
  have h : LinearMap.reduceModIdeal I
      (commutatorSymbol R A M N m D fun i ↦ (cotangentRep I (I.toCotangent (a i)) : A)) =
        LinearMap.reduceModIdeal I (commutatorSymbol R A M N m D fun i ↦ a i) :=
    reduceModIdeal_commutatorSymbol_eq D fun i ↦
      I.toCotangent_eq.1 (toCotangent_cotangentRep _)
  exact congr($h (Submodule.Quotient.mk x))

/-- The cotangent symbol is symmetric. -/
theorem cotangentSymbol_comp_perm {m : ℕ} (D : differentialOperators R A M N m)
    (ω : Fin m → I.Cotangent) (σ : Equiv.Perm (Fin m)) :
    cotangentSymbol R I D (ω ∘ σ) = cotangentSymbol R I D ω := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin m → I, (fun i ↦ I.toCotangent (a i)) = ω :=
    ⟨fun i ↦ cotangentRep I (ω i), funext fun i ↦ toCotangent_cotangentRep _⟩
  refine LinearMap.ext fun q ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  calc cotangentSymbol R I D ((fun i ↦ I.toCotangent (a i)) ∘ σ) (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (p := (I • ⊤ : Submodule A N))
          (commutatorSymbol R A M N m D ((fun i ↦ (a i : A)) ∘ σ) x) :=
        cotangentSymbol_toCotangent D (a ∘ σ) x
    _ = _ := by rw [commutatorSymbol_comp_perm, cotangentSymbol_toCotangent]

/-- Composition multiplies cotangent symbols on the diagonal: for `P` of order at most `m` and
`Q` of order at most `k`, the cotangent symbol of `P ∘ Q` at `(ω, …, ω)` is `(m + k).choose m`
times the composition of the cotangent symbols at `(ω, …, ω)`. -/
theorem cotangentSymbol_comp_const {m k : ℕ} (P : differentialOperators R A N O m)
    (Q : differentialOperators R A M N k) (ω : I.Cotangent) :
    cotangentSymbol R I
        ⟨(P : N →ₗ[R] O) ∘ₗ (Q : M →ₗ[R] N), comp_mem_differentialOperators P.2 Q.2⟩
        (fun _ ↦ ω) =
      (m + k).choose m •
        (cotangentSymbol R I P fun _ ↦ ω) ∘ₗ (cotangentSymbol R I Q fun _ ↦ ω) := by
  obtain ⟨y, rfl⟩ := I.toCotangent_surjective ω
  refine LinearMap.ext fun q ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have h := congr($(commutatorSymbol_comp_const P Q (y : A)) x)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply] at h
  simp only [LinearMap.smul_apply, LinearMap.comp_apply,
    cotangentSymbol_toCotangent _ (fun _ ↦ y), h, Submodule.Quotient.mk_smul]

end Cotangent

/-! ### The symbols at a rational point -/

section Point

variable {𝕜 A V : Type*} [Field 𝕜] [CommRing A] [Algebra 𝕜 A] [AddCommGroup V] [Module 𝕜 V]
  {J : Ideal A}

/-- The `𝕜`-linear map sending `a ∈ J` to the image of its cotangent class in `V`. -/
private def cotangentLinearMap (e : J.Cotangent ≃ₗ[𝕜] V) : J →ₗ[𝕜] V :=
  e.toLinearMap ∘ₗ J.toCotangent.restrictScalars 𝕜

private theorem exists_cotangentLinearMap_comp_eq_id (e : J.Cotangent ≃ₗ[𝕜] V) :
    ∃ s : V →ₗ[𝕜] J, cotangentLinearMap e ∘ₗ s = LinearMap.id :=
  (cotangentLinearMap e).exists_rightInverse_of_surjective <| LinearMap.range_eq_top.2 <|
    e.surjective.comp J.toCotangent_surjective

/-- A `𝕜`-linear choice of elements of `J` with prescribed images in `V`. -/
private noncomputable def cotangentLift (e : J.Cotangent ≃ₗ[𝕜] V) : V →ₗ[𝕜] J :=
  (exists_cotangentLinearMap_comp_eq_id e).choose

private theorem apply_toCotangent_cotangentLift (e : J.Cotangent ≃ₗ[𝕜] V) (v : V) :
    e (J.toCotangent (cotangentLift e v)) = v :=
  congr($((exists_cotangentLinearMap_comp_eq_id e).choose_spec) v)

/-- Every family of vectors of `V` is the image of a family of elements of `J`. -/
private theorem exists_apply_toCotangent_eq (e : J.Cotangent ≃ₗ[𝕜] V) {ι : Type*} (v : ι → V) :
    ∃ a : ι → J, (fun i ↦ e (J.toCotangent (a i))) = v :=
  ⟨fun i ↦ cotangentLift e (v i), funext fun i ↦ apply_toCotangent_cotangentLift e (v i)⟩

/-- The value under `φ` of the image of `1` under an `A`-linear endomorphism of `A`. -/
private def evalOneAt (φ : A →ₐ[𝕜] 𝕜) : (A →ₗ[A] A) →ₗ[𝕜] 𝕜 where
  toFun L := φ (L 1)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

variable (φ : A →ₐ[𝕜] 𝕜) (e : J.Cotangent ≃ₗ[𝕜] V)

/-- The commutator symbol of a differential operator `D` of order at most `m` on `A` at a
`𝕜`-point `φ : A →ₐ[𝕜] 𝕜` whose kernel contains `J`, read through an identification
`e : J / J² ≃ V`: the `𝕜`-multilinear form on `V` sending `(e [a₁], …, e [aₘ])`, for `aᵢ ∈ J`, to
`φ([⋯[D, a₁], …, aₘ] 1)` (`TauCeti.pointCommutatorSymbol_toCotangent`). For the vanishing ideal of a
point `x` of a manifold, evaluation at `x` and the identification of `J / J²` with the cotangent
space, this is the commutator symbol of `D` at `x`. -/
noncomputable def pointCommutatorSymbol {m : ℕ} :
    differentialOperators 𝕜 A A A m →ₗ[𝕜] MultilinearMap (RingHom.id 𝕜) (fun _ : Fin m ↦ V) 𝕜 where
  toFun D := ((evalOneAt φ).compMultilinearMap (commutatorSymbol 𝕜 A A A m D)).compLinearMap
    fun _ ↦ J.subtype.restrictScalars 𝕜 ∘ₗ cotangentLift e
  map_add' D₁ D₂ := by ext; simp
  map_smul' c D := by ext; simp

variable {φ}

/-- The point commutator symbol at the classes of `a₁, …, aₘ ∈ J` is `φ([⋯[D, a₁], …, aₘ] 1)`. -/
theorem pointCommutatorSymbol_toCotangent (hJ : J ≤ RingHom.ker φ) {m : ℕ}
    (D : differentialOperators 𝕜 A A A m) (a : Fin m → J) :
    pointCommutatorSymbol φ e D (fun i ↦ e (J.toCotangent (a i))) =
      φ (commutatorSymbol 𝕜 A A A m D (fun i ↦ a i) 1) := by
  -- The chosen lifts differ from the `aᵢ` by elements of `J²`.
  have h := commutatorSymbol_apply_sub_mem_smul_top (I := J) D
    (a := fun i ↦ (cotangentLift e (e (J.toCotangent (a i))) : A)) (b := fun i ↦ a i)
    (fun i ↦ J.toCotangent_eq.1 <| e.injective <| apply_toCotangent_cotangentLift e _) 1
  rw [smul_eq_mul, Ideal.mul_top] at h
  exact sub_eq_zero.1 ((map_sub φ _ _).symm.trans (RingHom.mem_ker.1 (hJ h)))

/-- The point commutator symbol is symmetric. -/
theorem pointCommutatorSymbol_comp_perm (hJ : J ≤ RingHom.ker φ) {m : ℕ}
    (D : differentialOperators 𝕜 A A A m) (v : Fin m → V) (σ : Equiv.Perm (Fin m)) :
    pointCommutatorSymbol φ e D (v ∘ σ) = pointCommutatorSymbol φ e D v := by
  obtain ⟨a, rfl⟩ := exists_apply_toCotangent_eq e v
  calc pointCommutatorSymbol φ e D ((fun i ↦ e (J.toCotangent (a i))) ∘ σ)
      = φ (commutatorSymbol 𝕜 A A A m D ((fun i ↦ (a i : A)) ∘ σ) 1) :=
        pointCommutatorSymbol_toCotangent e hJ D (a ∘ σ)
    _ = _ := by rw [commutatorSymbol_comp_perm, pointCommutatorSymbol_toCotangent e hJ]

/-- **Comparison with the cotangent symbol.** When `J` is the kernel of `φ`, the class modulo `J`
of the scalar `σ(e u₁, …, e uₘ)` is the image of the class of `1` under the cotangent symbol at
`(u₁, …, uₘ)`. -/
theorem mk_algebraMap_pointCommutatorSymbol (hJ : RingHom.ker φ = J) {m : ℕ}
    (D : differentialOperators 𝕜 A A A m) (u : Fin m → J.Cotangent) :
    Submodule.Quotient.mk (p := (J • ⊤ : Submodule A A))
        (algebraMap 𝕜 A (pointCommutatorSymbol φ e D fun i ↦ e (u i))) =
      cotangentSymbol 𝕜 J D u (Submodule.Quotient.mk 1) := by
  choose a ha using fun i ↦ J.toCotangent_surjective (u i)
  obtain rfl : (fun i ↦ J.toCotangent (a i)) = u := funext ha
  rw [pointCommutatorSymbol_toCotangent e hJ.ge, cotangentSymbol_toCotangent,
    Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top]
  apply hJ.le
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_self]

/-- The point commutator symbol of an operator of order at most `m + 1` vanishes if the operator
has order at most `m`. -/
theorem pointCommutatorSymbol_eq_zero_of_mem_differentialOperators (hJ : J ≤ RingHom.ker φ)
    {m : ℕ} (D : differentialOperators 𝕜 A A A (m + 1))
    (hD : (D : A →ₗ[𝕜] A) ∈ differentialOperators 𝕜 A A A m) :
    pointCommutatorSymbol φ e D = 0 := by
  ext v
  obtain ⟨a, rfl⟩ := exists_apply_toCotangent_eq e v
  simp [pointCommutatorSymbol_toCotangent e hJ, (commutatorSymbol_eq_zero_iff D).2 hD]

variable (φ)

/-- The principal symbol of a differential operator `D` of order at most `m` on `A` at a
`𝕜`-point `φ`, read through `e : J / J² ≃ V`: the homogeneous function `v ↦ (1 / m!) σ(v, …, v)`
of degree `m` on `V`, where `σ` is the point commutator symbol
`TauCeti.pointCommutatorSymbol φ e D`. At the class of `a ∈ J` it is `(1 / m!) φ([⋯[D, a], …, a] 1)`
with `m` copies of `a`. -/
noncomputable def pointPrincipalSymbol {m : ℕ} (D : differentialOperators 𝕜 A A A m) (v : V) : 𝕜 :=
  (m.factorial : 𝕜)⁻¹ * pointCommutatorSymbol φ e D fun _ ↦ v

theorem pointPrincipalSymbol_def {m : ℕ} (D : differentialOperators 𝕜 A A A m) (v : V) :
    pointPrincipalSymbol φ e D v = (m.factorial : 𝕜)⁻¹ * pointCommutatorSymbol φ e D fun _ ↦ v :=
  (rfl)

@[simp]
theorem pointPrincipalSymbol_zero {m : ℕ} (v : V) :
    pointPrincipalSymbol φ e (0 : differentialOperators 𝕜 A A A m) v = 0 := by
  simp [pointPrincipalSymbol_def]

@[simp]
theorem pointPrincipalSymbol_add {m : ℕ} (D₁ D₂ : differentialOperators 𝕜 A A A m) (v : V) :
    pointPrincipalSymbol φ e (D₁ + D₂) v =
      pointPrincipalSymbol φ e D₁ v + pointPrincipalSymbol φ e D₂ v := by
  simp [pointPrincipalSymbol_def, mul_add]

@[simp]
theorem pointPrincipalSymbol_smul {m : ℕ} (c : 𝕜) (D : differentialOperators 𝕜 A A A m) (v : V) :
    pointPrincipalSymbol φ e (c • D) v = c * pointPrincipalSymbol φ e D v := by
  simp only [pointPrincipalSymbol_def, map_smul, smul_apply, smul_eq_mul]
  ring

/-- The point principal symbol of an operator of order at most `m` is homogeneous of degree `m`. -/
theorem pointPrincipalSymbol_smul_covector {m : ℕ} (D : differentialOperators 𝕜 A A A m) (c : 𝕜)
    (v : V) : pointPrincipalSymbol φ e D (c • v) = c ^ m * pointPrincipalSymbol φ e D v := by
  have h := (pointCommutatorSymbol φ e D).map_smul_univ (fun _ ↦ c) fun _ ↦ v
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    RingHom.id_apply] at h
  rw [pointPrincipalSymbol_def, pointPrincipalSymbol_def, h]
  ring

variable {φ}

/-- The point principal symbol of an operator of order at most `m + 1` vanishes if the operator
has order at most `m`. -/
theorem pointPrincipalSymbol_eq_zero_of_mem_differentialOperators (hJ : J ≤ RingHom.ker φ)
    {m : ℕ} (D : differentialOperators 𝕜 A A A (m + 1))
    (hD : (D : A →ₗ[𝕜] A) ∈ differentialOperators 𝕜 A A A m) (v : V) :
    pointPrincipalSymbol φ e D v = 0 := by
  simp [pointPrincipalSymbol_def,
    pointCommutatorSymbol_eq_zero_of_mem_differentialOperators e hJ D hD]

/-- **Principal symbols multiply under composition.** For operators `P` and `Q` of orders at most
`m` and `k`, the point principal symbol of `P ∘ Q`, as an operator of order at most `m + k`, is the
product of the point principal symbols. -/
theorem pointPrincipalSymbol_comp [CharZero 𝕜] (hJ : J ≤ RingHom.ker φ) {m k : ℕ}
    (P : differentialOperators 𝕜 A A A m) (Q : differentialOperators 𝕜 A A A k) (v : V) :
    pointPrincipalSymbol φ e
        ⟨(P : A →ₗ[𝕜] A) ∘ₗ (Q : A →ₗ[𝕜] A), comp_mem_differentialOperators P.2 Q.2⟩ v =
      pointPrincipalSymbol φ e P v * pointPrincipalSymbol φ e Q v := by
  obtain ⟨a, rfl⟩ : ∃ a : J, e (J.toCotangent a) = v :=
    ⟨cotangentLift e v, apply_toCotangent_cotangentLift e v⟩
  -- The `(m + k)`-fold commutator of `P ∘ Q` with `a` is `(m + k).choose m` times the product of
  -- the commutators of `P` and `Q`, and `(m + k).choose m / (m + k)! = 1 / (m! k!)`.
  have key : φ (commutatorSymbol 𝕜 A A A (m + k)
      ⟨(P : A →ₗ[𝕜] A) ∘ₗ (Q : A →ₗ[𝕜] A), comp_mem_differentialOperators P.2 Q.2⟩
      (fun _ ↦ (a : A)) 1) = (m + k).choose m * (φ (commutatorSymbol 𝕜 A A A m P (fun _ ↦ a) 1) *
        φ (commutatorSymbol 𝕜 A A A k Q (fun _ ↦ a) 1)) := by
    rw [commutatorSymbol_comp_const, LinearMap.smul_apply, map_nsmul, LinearMap.comp_apply,
      ← Dual.apply_one_mul_eq (commutatorSymbol 𝕜 A A A m P fun _ ↦ a), map_mul, nsmul_eq_mul]
  simp only [pointPrincipalSymbol_def, pointCommutatorSymbol_toCotangent e hJ _ fun _ ↦ a]
  have hfac (n : ℕ) : (n.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  rw [key, Nat.cast_add_choose]
  field_simp [hfac]

end Point

/-! ### The second derivative on polynomials -/

open Polynomial in
/-- The commutator symbol of the second derivative on `R[X]` at `(X, X)` is multiplication by
`2`. When `2` is invertible in `R`, dividing by `2!` gives the value `1` of the principal symbol
of `∂²` at `dX`. -/
theorem _root_.Polynomial.commutatorSymbol_derivative_comp_derivative {R : Type*} [CommRing R]
    (p : R[X]) :
    commutatorSymbol R R[X] R[X] R[X] 2
      ⟨derivative ∘ₗ derivative, derivative_comp_derivative_mem_differentialOperators_two⟩
      ![X, X] p = 2 * p := by
  have h1 : commutatorSymbol R R[X] R[X] R[X] 2
      ⟨derivative ∘ₗ derivative, derivative_comp_derivative_mem_differentialOperators_two⟩
      ![X, X] 1 = 2 := by
    rw [commutatorSymbol_apply_apply, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, List.prod_cons, List.prod_nil, mul_one,
      mul_apply_eq_comp, smulCommutator_apply_apply, LinearMap.comp_apply, smul_eq_mul]
    simp only [mul_one, derivative_mul, derivative_X, derivative_one]
    simp [one_add_one_eq_two]
  conv_lhs => rw [← mul_one p, ← smul_eq_mul, map_smul, h1]
  rw [smul_eq_mul, mul_comm]

end TauCeti
