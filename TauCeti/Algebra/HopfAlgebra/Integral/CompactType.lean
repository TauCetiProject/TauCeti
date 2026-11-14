/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Decomposition
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.PositiveIntegral
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Transport
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Trivial
public import TauCeti.Algebra.Coalgebra.Comodule.Unitary.Orthogonality

/-!
# Sweedler's invariant integral and compact-type Hopf star algebras

Every bialgebra `A` over a field `k` that is spanned by its simple matrix-coefficient submodules—in
particular, every linearly reductive bialgebra—is the internal direct sum of its distinct simple
coefficient spaces, with the line `k · 1` appearing as the coefficient space of the trivial
rank-one comodule. Projecting onto `k · 1` via the counit and annihilating all nontrivial simple
blocks defines Sweedler's normalized two-sided invariant integral `TauCeti.sweedlerIntegral`.

Over `ℂ`, combining Sweedler's invariant integral with unitarization, complete reducibility of
unitary comodules, cross-orthogonality, and weighted Schur orthogonality yields the Dijkhuizen–
Koornwinder characterization (`TauCeti.compactType_iff`) of compact-type Hopf star algebras: a
complex Hopf star algebra admits an algebraic Haar functional (`TauCeti.AlgebraicHaar`) if and only
if it is spanned as a complex vector space by the matrix entries of its finite-dimensional unitary
matrix corepresentations (`TauCeti.unitaryCoefficientSet`).

## Main declarations

* `TauCeti.Comodule.span_singleton_one_mem_simpleCoefficientSubmodules`: the line `k · 1` is a
  simple matrix-coefficient submodule of any bialgebra over a field.
* `TauCeti.sweedlerIntegral`: the normalized two-sided invariant integral on a bialgebra over a
  field spanned by its simple coefficient submodules, with
  `TauCeti.isLeftInvariantIntegral_sweedlerIntegral` and
  `TauCeti.isRightInvariantIntegral_sweedlerIntegral`.
* `TauCeti.Coalgebra.IsLinearlyReductive.existsUnique_twoSidedInvariantIntegral`: existence and
  uniqueness of a normalized two-sided invariant integral on a linearly reductive bialgebra.
* `TauCeti.unitaryCoefficientSet`: the set of entries of unitary `Fin n × Fin n` coefficient
  matrices over a complex star coalgebra.
* `TauCeti.compactType_iff`: a complex Hopf star algebra admits an `AlgebraicHaar` functional if
  and only if `unitaryCoefficientSet A` spans `A` over `ℂ`.

## References

* M. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, Chapter XIV.
* M. S. Dijkhuizen and T. H. Koornwinder, *CQG algebras: a direct algebraic approach to compact
  quantum groups*, Lett. Math. Phys. 32 (1994), 315–330.
* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Theorem 3.2.12.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Theorem 1.6.6.
-/

public noncomputable section

open Module Matrix TauCeti.Comodule
open scoped TensorProduct ComplexOrder DirectSum

namespace TauCeti

namespace Comodule

section Field

universe u v

variable {k : Type u} [Field k]

/-- A coalgebra over a field that is spanned by its distinct simple coefficient spaces is their
internal direct sum. -/
theorem isInternal_of_sSup_simpleCoefficientSubmodules_eq_top
    {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    (hspan : sSup (simpleCoefficientSubmodules k C) = ⊤) :
    DirectSum.IsInternal (fun P : simpleCoefficientSubmodules k C ↦ (P.1 : Submodule k C)) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (sSupIndep_iff _).mp sSupIndep_simpleCoefficientSubmodules
  · rwa [← sSup_eq_iSup']

/-- Over any bialgebra `A` over a field `k`, the line `Submodule.span k {1}` belongs to
`simpleCoefficientSubmodules k A` as the coefficient space of the trivial rank-one comodule. -/
theorem span_singleton_one_mem_simpleCoefficientSubmodules
    {A : Type v} [Ring A] [Bialgebra k A] :
    Submodule.span k ({1} : Set A) ∈ simpleCoefficientSubmodules k A := by
  let _ : Comodule k A k := Comodule.trivial
  have : Nontrivial (Subcomodule k A k) :=
    ⟨⟨⊥, ⊤, fun h ↦ one_ne_zero (Subcomodule.mem_bot.mp (h.symm ▸ Subcomodule.mem_top (1 : k)))⟩⟩
  have : IsSimpleOrder (Subcomodule k A k) :=
    ⟨fun S ↦ (eq_bot_or_eq_top S.toSubmodule).imp
      Subcomodule.toSubmodule_eq_bot.mp Subcomodule.toSubmodule_eq_top.mp⟩
  let L : Submodule k A := Submodule.span k ({1} : Set A)
  let e : k ≃ₗ[k] L :=
    { toFun c := ⟨c • 1, Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton 1))⟩
      invFun x := Coalgebra.counit (R := k) x.1
      left_inv c := by simp
      right_inv x := Subtype.ext <| by
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
        simp [← hc]
      map_add' x y := Subtype.ext (add_smul x y 1)
      map_smul' r x := Subtype.ext (mul_smul r x 1) }
  let _ : Comodule k A L := Comodule.Transport e
  have : IsSimpleOrder (Subcomodule k A L) :=
    (Subcomodule.transportOrderIso e).symm.isSimpleOrder
  have hL : matrixCoefficientSubmodule (R := k) (C := A) (M := L) = L := by
    rw [matrixCoefficientSubmodule_transport e,
      trivial_rankOne_matrixCoefficientSubmodule_eq_span_singleton_one]
  exact mem_simpleCoefficientSubmodules.mpr ⟨ComoduleCat.of k A L, inferInstance, hL.symm⟩

end Field

end Comodule

section SweedlerIntegral

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Bialgebra k A]

/-- **Sweedler's invariant integral** on a bialgebra `A` over a field `k` whose simple coefficient
submodules span `A`: the `k`-linear functional equal to `Coalgebra.counit` on `k · 1` and `0` on
every nontrivial simple coefficient submodule. -/
def sweedlerIntegral (hspan : sSup (Comodule.simpleCoefficientSubmodules k A) = ⊤) :
    A →ₗ[k] k :=
  (Coalgebra.counit (R := k) (A := A) ∘ₗ (Submodule.span k ({1} : Set A)).subtype) ∘ₗ
    DirectSum.component k (Comodule.simpleCoefficientSubmodules k A)
      (fun P ↦ (P.1 : Submodule k A))
      ⟨Submodule.span k ({1} : Set A),
        Comodule.span_singleton_one_mem_simpleCoefficientSubmodules⟩ ∘ₗ
    (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap fun P : Comodule.simpleCoefficientSubmodules k A ↦
        (P.1 : Submodule k A))
      (Comodule.isInternal_of_sSup_simpleCoefficientSubmodules_eq_top hspan)).symm.toLinearMap

/-- On `k · 1`, `sweedlerIntegral` agrees with the counit. -/
theorem sweedlerIntegral_apply_of_mem_span_one
    (hspan : sSup (Comodule.simpleCoefficientSubmodules k A) = ⊤)
    {x : A} (hx : x ∈ Submodule.span k ({1} : Set A)) :
    sweedlerIntegral hspan x = Coalgebra.counit (R := k) x := by
  let hInt := Comodule.isInternal_of_sSup_simpleCoefficientSubmodules_eq_top hspan
  let P₁ : Comodule.simpleCoefficientSubmodules k A :=
    ⟨Submodule.span k ({1} : Set A), Comodule.span_singleton_one_mem_simpleCoefficientSubmodules⟩
  have hcomp := hInt.ofBijective_coeLinearMap_of_mem (i := P₁) hx
  simpa [sweedlerIntegral, P₁, ← DirectSum.apply_eq_component] using
    congrArg (fun y : P₁.1 ↦ Coalgebra.counit (R := k) (y : A)) hcomp

/-- On every simple coefficient submodule distinct from `k · 1`, `sweedlerIntegral` vanishes. -/
theorem sweedlerIntegral_apply_of_mem_of_ne
    (hspan : sSup (Comodule.simpleCoefficientSubmodules k A) = ⊤)
    {P : Submodule k A} (hP : P ∈ Comodule.simpleCoefficientSubmodules k A)
    (hPne : P ≠ Submodule.span k ({1} : Set A)) {x : A} (hx : x ∈ P) :
    sweedlerIntegral hspan x = 0 := by
  let hInt := Comodule.isInternal_of_sSup_simpleCoefficientSubmodules_eq_top hspan
  let P₁ : Comodule.simpleCoefficientSubmodules k A :=
    ⟨Submodule.span k ({1} : Set A), Comodule.span_singleton_one_mem_simpleCoefficientSubmodules⟩
  let Q : Comodule.simpleCoefficientSubmodules k A := ⟨P, hP⟩
  have hQne : Q ≠ P₁ := fun h ↦ hPne (congrArg Subtype.val h)
  have hcomp := hInt.ofBijective_coeLinearMap_of_mem_ne (i := Q) (j := P₁) hQne hx
  simpa [sweedlerIntegral, P₁, ← DirectSum.apply_eq_component] using
    congrArg (fun y : P₁.1 ↦ Coalgebra.counit (R := k) (y : A)) hcomp

/-- `sweedlerIntegral` evaluates to `1` at `1`. -/
@[simp]
theorem sweedlerIntegral_one (hspan : sSup (Comodule.simpleCoefficientSubmodules k A) = ⊤) :
    sweedlerIntegral hspan 1 = 1 := by
  rw [sweedlerIntegral_apply_of_mem_span_one hspan (Submodule.subset_span (Set.mem_singleton 1)),
    Bialgebra.counit_one]

/-- `sweedlerIntegral` recovers scalar multiples of `1`. -/
@[simp]
theorem sweedlerIntegral_algebraMap (hspan : sSup (Comodule.simpleCoefficientSubmodules k A) = ⊤)
    (c : k) :
    sweedlerIntegral hspan (algebraMap k A c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, sweedlerIntegral_one, smul_eq_mul, mul_one]

private theorem linearMap_eq_of_sweedlerIntegral
    (hspan : sSup (Comodule.simpleCoefficientSubmodules k A) = ⊤)
    {F G : A →ₗ[k] A} (h1 : F 1 = G 1)
    (hmat : ∀ {M : ComoduleCat.{u, v, v} k A} [IsSimpleOrder (Subcomodule k A M)]
      {n : ℕ} (b : Basis (Fin n) k M),
      (∀ p q, sweedlerIntegral hspan (coefficientMatrix (C := A) b p q) = 0) →
      ∀ i j, F (coefficientMatrix (C := A) b i j) = G (coefficientMatrix (C := A) b i j))
    (a : A) : F a = G a := by
  suffices hFG : LinearMap.eqLocus F G = ⊤ from
    LinearMap.mem_eqLocus.mp (hFG ▸ Submodule.mem_top)
  rw [eq_top_iff, ← hspan]
  refine sSup_le fun P hP ↦ ?_
  by_cases hP1 : P = Submodule.span k ({1} : Set A)
  · rw [hP1, Submodule.span_le, Set.singleton_subset_iff]
    exact h1
  · obtain ⟨M, hM, rfl⟩ := mem_simpleCoefficientSubmodules.mp hP
    let _ := hM
    have : Module.Finite k M := Comodule.finite_of_isSimpleOrder (C := A)
    let b := Module.finBasis k M
    have hzero (p q) : sweedlerIntegral hspan (coefficientMatrix (C := A) b p q) = 0 := by
      refine sweedlerIntegral_apply_of_mem_of_ne hspan
        matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules hP1 ?_
      rw [coefficientMatrix_apply]
      exact matrixCoefficient_mem_submodule _ _
    intro x hx
    obtain ⟨X, rfl⟩ := (Comodule.mem_matrixCoefficientSubmodule_iff_exists_matrix b).mp hx
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (LinearMap.mem_eqLocus.mpr (hmat b hzero i j))

/-- `sweedlerIntegral` is a left invariant integral. -/
theorem isLeftInvariantIntegral_sweedlerIntegral
    (hspan : sSup (Comodule.simpleCoefficientSubmodules k A) = ⊤) :
    (sweedlerIntegral hspan).IsLeftInvariantIntegral := by
  rw [LinearMap.isLeftInvariantIntegral_iff]
  set h := sweedlerIntegral hspan
  let F : A →ₗ[k] A := (TensorProduct.rid k A).toLinearMap ∘ₗ h.lTensor A ∘ₗ Coalgebra.comul
  let G : A →ₗ[k] A := Algebra.linearMap k A ∘ₗ h
  intro a
  have ha : F a = G a := linearMap_eq_of_sweedlerIntegral hspan
    (by simp [F, G, Bialgebra.comul_one, Algebra.TensorProduct.one_def, h, sweedlerIntegral_one])
    (fun b hzero i j ↦ by simp [F, G, comul_coefficientMatrix_eq_sum b i j, h, hzero]) a
  simpa [F, G, Algebra.algebraMap_eq_smul_one] using ha

/-- `sweedlerIntegral` is a right invariant integral. -/
theorem isRightInvariantIntegral_sweedlerIntegral
    (hspan : sSup (Comodule.simpleCoefficientSubmodules k A) = ⊤) :
    (sweedlerIntegral hspan).IsRightInvariantIntegral := by
  rw [LinearMap.isRightInvariantIntegral_iff]
  set h := sweedlerIntegral hspan
  let F : A →ₗ[k] A := (TensorProduct.lid k A).toLinearMap ∘ₗ h.rTensor A ∘ₗ Coalgebra.comul
  let G : A →ₗ[k] A := Algebra.linearMap k A ∘ₗ h
  intro a
  have ha : F a = G a := linearMap_eq_of_sweedlerIntegral hspan
    (by simp [F, G, Bialgebra.comul_one, Algebra.TensorProduct.one_def, h, sweedlerIntegral_one])
    (fun b hzero i j ↦ by simp [F, G, comul_coefficientMatrix_eq_sum b i j, h, hzero]) a
  simpa [F, G, Algebra.algebraMap_eq_smul_one] using ha

/-- Every linearly reductive bialgebra over a field admits a unique normalized two-sided invariant
integral. -/
theorem Coalgebra.IsLinearlyReductive.existsUnique_twoSidedInvariantIntegral
    (hLR : Coalgebra.IsLinearlyReductive.{u, v, u} k A) :
    ∃! h : A →ₗ[k] k,
      h.IsLeftInvariantIntegral ∧ h.IsRightInvariantIntegral ∧ h 1 = 1 := by
  have hspan := hLR.sSup_simpleCoefficientSubmodules_eq_top
  refine ⟨sweedlerIntegral hspan,
    ⟨isLeftInvariantIntegral_sweedlerIntegral hspan,
      isRightInvariantIntegral_sweedlerIntegral hspan,
      sweedlerIntegral_one hspan⟩, ?_⟩
  rintro h' ⟨hl', _, h1'⟩
  exact hl'.eq_of_isRightInvariantIntegral
    (isRightInvariantIntegral_sweedlerIntegral hspan) h1' (sweedlerIntegral_one hspan)

/-- On a Hopf algebra over a field, `sweedlerIntegral` is invariant under the antipode. -/
@[simp]
theorem sweedlerIntegral_antipode {H : Type v} [Ring H] [HopfAlgebra k H]
    (hspan : sSup (Comodule.simpleCoefficientSubmodules k H) = ⊤) (a : H) :
    sweedlerIntegral hspan (HopfAlgebra.antipode k a) = sweedlerIntegral hspan a :=
  (isRightInvariantIntegral_sweedlerIntegral hspan).map_antipode (sweedlerIntegral_one hspan) a

end SweedlerIntegral

section CompactType

universe u

/-- The set of matrix entries of all finite-dimensional unitary matrix corepresentations on
`Fin n → ℂ` of a complex star coalgebra `A`. -/
def unitaryCoefficientSet (A : Type u) [Semiring A] [Algebra ℂ A] [Coalgebra ℂ A]
    [StarRing A] : Set A :=
  {a : A | ∃ (n : ℕ) (ρ : Comodule ℂ A (Fin n → ℂ)),
    letI := ρ
    let U := Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin n))
    U ∈ unitary (Matrix (Fin n) (Fin n) A) ∧ ∃ i j, a = U i j}

/-- Membership in `unitaryCoefficientSet A` unfolds to being an entry of a unitary `Fin n × Fin n`
coefficient matrix. -/
theorem mem_unitaryCoefficientSet_iff {A : Type u} [Semiring A] [Algebra ℂ A] [Coalgebra ℂ A]
    [StarRing A] {a : A} :
    a ∈ unitaryCoefficientSet A ↔
      ∃ (n : ℕ) (ρ : Comodule ℂ A (Fin n → ℂ)),
        letI := ρ
        let U := Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin n))
        U ∈ unitary (Matrix (Fin n) (Fin n) A) ∧ ∃ i j, a = U i j :=
  Iff.rfl

/-- Every entry of a unitary coefficient matrix in a `Fin n`-indexed basis belongs to
`unitaryCoefficientSet A`. -/
theorem _root_.Module.Basis.coefficientMatrix_mem_unitaryCoefficientSet
    {A M : Type*} {n : ℕ} [Semiring A] [Algebra ℂ A] [Coalgebra ℂ A] [StarRing A]
    [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M] (b : Basis (Fin n) ℂ M)
    (hb : coefficientMatrix (C := A) b ∈ unitary (Matrix (Fin n) (Fin n) A))
    (i j : Fin n) :
    coefficientMatrix (C := A) b i j ∈ unitaryCoefficientSet A :=
  ⟨n, Comodule.Transport b.equivFun,
    by rwa [Comodule.coefficientMatrix_basisFun_transport_equivFun b],
    i, j, by simp [Comodule.coefficientMatrix_basisFun_transport_equivFun b]⟩

section HopfStarAlgebra

variable {A : Type u} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]

omit [StarRing A] [StarModule ℂ A] [StarCoalgebra ℂ A] in
private theorem finMatrix_mem_simpleCoefficientSubmodules {m : ℕ}
    [Comodule ℂ A (Fin m → ℂ)] [IsSimpleOrder (Subcomodule ℂ A (Fin m → ℂ))] :
    matrixCoefficientSubmodule (R := ℂ) (C := A) (M := Fin m → ℂ) ∈
      simpleCoefficientSubmodules ℂ A := by
  let e : (Fin m → ℂ) ≃ₗ[ℂ] (ULift.{u} (Fin m) → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ Equiv.ulift
  let _ : Comodule ℂ A (ULift.{u} (Fin m) → ℂ) := Comodule.Transport e
  have : IsSimpleOrder (Subcomodule ℂ A (ULift.{u} (Fin m) → ℂ)) :=
    (Subcomodule.transportOrderIso e).symm.isSimpleOrder
  rw [← matrixCoefficientSubmodule_transport e]
  exact matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules

private theorem conjFinMatrix_mem_simpleCoefficientSubmodules {m : ℕ}
    [Comodule ℂ A (Fin m → ℂ)] [IsSimpleOrder (Subcomodule ℂ A (Fin m → ℂ))] :
    (letI : Comodule ℂ A (Fin m → ℂ) := conjugateMatrixComodule (A := A) (Pi.basisFun ℂ (Fin m));
      matrixCoefficientSubmodule (R := ℂ) (C := A) (M := Fin m → ℂ)) ∈
        simpleCoefficientSubmodules ℂ A := by
  have := isSimpleOrder_conjugateMatrixComodule (A := A) (Pi.basisFun ℂ (Fin m))
  let _ : Comodule ℂ A (Fin m → ℂ) := conjugateMatrixComodule (A := A) (Pi.basisFun ℂ (Fin m))
  exact finMatrix_mem_simpleCoefficientSubmodules

/-- If a simple unitary comodule `M` has conjugate coefficient space equal to the coefficient space
of another simple unitary comodule `N`, then any normalized two-sided invariant integral `h` is
nonnegative on `star x * x` for `x` in the coefficient space of `M`. -/
private theorem map_star_mul_self_nonneg_of_conj_unitary
    {M N ι κ : Type*} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
    [IsSimpleOrder (Subcomodule ℂ A M)] [AddCommGroup N] [Module ℂ N] [Comodule ℂ A N]
    [IsSimpleOrder (Subcomodule ℂ A N)] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {h : A →ₗ[ℂ] ℂ} (hl : h.IsLeftInvariantIntegral) (hr : h.IsRightInvariantIntegral)
    (h1 : h 1 = 1) (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (c : Basis κ ℂ N) (hv : coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A))
    (hconj : (letI := conjugateMatrixComodule (A := A) b;
      matrixCoefficientSubmodule (R := ℂ) (C := A) (M := ι → ℂ)) =
        matrixCoefficientSubmodule (R := ℂ) (C := A) (M := N))
    {x : A} (hx : x ∈ matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M)) :
    0 ≤ h (star x * x) := by
  let _ : Comodule ℂ A (ι → ℂ) := conjugateMatrixComodule (A := A) b
  have : IsSimpleOrder (Subcomodule ℂ A (ι → ℂ)) := isSimpleOrder_conjugateMatrixComodule (A := A) b
  obtain ⟨φ, hφ⟩ :=
    (matrixCoefficientSubmodule_eq_iff (R := ℂ) (C := A) (M := ι → ℂ) (N := N)).mp hconj
  let T : Matrix κ ι ℂ := LinearMap.toMatrix (Pi.basisFun ℂ ι) c φ.toLinearMap
  have hTv (v : ι → ℂ) : T *ᵥ v = ⇑(c.repr (φ v)) := by
    simpa [T, funext (Pi.basisFun_repr ℂ ι v)] using
      φ.toLinearMap.toMatrix_mulVec_repr (Pi.basisFun ℂ ι) c v
  have hT_inj : Function.Injective T.mulVec := fun v w hvw ↦
    (φ.bijective_of_ne_zero hφ).1 <| c.repr.injective <|
      DFunLike.coe_injective ((hTv v).symm.trans (hvw.trans (hTv w)))
  let G : Matrix ι ι ℂ := Tᴴ * T
  have hG : G.PosDef := Matrix.PosDef.conjTranspose_mul_self T hT_inj
  have hfv :
      coefficientMatrix (C := A) c * T.map (algebraMap ℂ A) =
        T.map (algebraMap ℂ A) * (coefficientMatrix (C := A) b).map star := by
    simpa [T, coefficientMatrix_conjugateMatrixComodule] using
      φ.coefficientMatrix_mul_toMatrix (Pi.basisFun ℂ ι) c
  have hGinv :
      ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
        (coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A) := by
    set f := algebraMap ℂ A
    have hv1 : (coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hv).1
    have hGf : G.map f = (T.map f)ᴴ * T.map f := by
      rw [Matrix.map_mul, Matrix.conjTranspose_map _ fun z ↦ algebraMap_star_comm z]
    calc ((coefficientMatrix (C := A) b).map star)ᴴ * G.map f *
          (coefficientMatrix (C := A) b).map star
        = (T.map f * (coefficientMatrix (C := A) b).map star)ᴴ *
            (T.map f * (coefficientMatrix (C := A) b).map star) := by
            simp only [hGf, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (T.map f)ᴴ * ((coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c) *
            T.map f := by simp only [← hfv, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G.map f := by rw [hv1, Matrix.mul_one, hGf]
  exact b.map_star_mul_self_nonneg_of_conjInvariant hl hr h1 hu hG hGinv hx

/-- If a complex Hopf star algebra admits an `AlgebraicHaar` functional, then the matrix entries of
its finite-dimensional unitary comodules span `A`. -/
theorem AlgebraicHaar.span_unitaryCoefficientSet_eq_top (h : AlgebraicHaar A) :
    Submodule.span ℂ (unitaryCoefficientSet A) = ⊤ := by
  have hLR : Coalgebra.IsLinearlyReductive.{0, u, 0} ℂ A :=
    h.isRightInvariantIntegral.isLinearlyReductive h.toLinearMap_ne_zero h.map_star_mul_self_nonneg
  rw [eq_top_iff, ← hLR.sSup_simpleCoefficientSubmodules_eq_top]
  refine sSup_le fun P hP ↦ ?_
  obtain ⟨M, hM, rfl⟩ := mem_simpleCoefficientSubmodules.mp hP
  let _ := hM
  have : Module.Finite ℂ M := Comodule.finite_of_isSimpleOrder (C := A)
  obtain ⟨b, hb⟩ := Comodule.exists_basis_coefficientMatrix_mem_unitary
    h.isRightInvariantIntegral h.toLinearMap_ne_zero h.map_star_mul_self_nonneg
    (Module.finBasis ℂ M)
  intro x hx
  obtain ⟨X, rfl⟩ := (Comodule.mem_matrixCoefficientSubmodule_iff_exists_matrix b).mp hx
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem _ _
      (Submodule.subset_span (b.coefficientMatrix_mem_unitaryCoefficientSet hb i j))

private def simpleUnitaryCoefficientSubmodules (A : Type u) [Ring A] [StarRing A] [Bialgebra ℂ A] :
    Set (Submodule ℂ A) :=
  {P ∈ simpleCoefficientSubmodules ℂ A |
    ∃ (m : ℕ) (ρ : Comodule ℂ A (Fin m → ℂ)),
      letI := ρ
      IsSimpleOrder (Subcomodule ℂ A (Fin m → ℂ)) ∧
      coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin m)) ∈
        unitary (Matrix (Fin m) (Fin m) A) ∧
      P = matrixCoefficientSubmodule (R := ℂ) (C := A) (M := Fin m → ℂ)}

omit [StarCoalgebra ℂ A] in
private theorem sSup_simpleUnitaryCoefficientSubmodules_eq_top
    (hspan : Submodule.span ℂ (unitaryCoefficientSet A) = ⊤) :
    sSup (simpleUnitaryCoefficientSubmodules A) = ⊤ := by
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro a ⟨n, ρ, hU, i, j, rfl⟩
  let _ := ρ
  let bE : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℂ
  let fE : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := bE.toBasis.equivFun.symm
  let _ : Comodule ℂ A (EuclideanSpace ℂ (Fin n)) := Comodule.Transport fE
  have hbE_map : (Pi.basisFun ℂ (Fin n)).map fE = bE.toBasis :=
    DFunLike.ext _ _ fun k ↦ bE.toBasis.equivFun.injective <| funext fun l ↦ by
      simp [fE, Pi.basisFun_apply, eq_comm]
  have hbE_mat : coefficientMatrix (C := A) bE.toBasis =
      coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin n)) := by
    rw [← hbE_map, Comodule.coefficientMatrix_map_transport]
  have hUnit : IsUnitary ℂ A (EuclideanSpace ℂ (Fin n)) :=
    bE.isUnitary_comodule_iff.mpr (hbE_mat.symm ▸ hU)
  have hatoms : sSup {W : Subcomodule ℂ A (EuclideanSpace ℂ (Fin n)) | IsAtom W} = ⊤ :=
    isCompletelyReducible_iff_sSup_atoms_eq_top.mp hUnit.isCompletelyReducible
  have hv : bE.toBasis j ∈
      ⨆ W : {W : Subcomodule ℂ A (EuclideanSpace ℂ (Fin n)) | IsAtom W}, W.1.toSubmodule := by
    rw [← Subcomodule.sSup_toSubmodule, hatoms, Subcomodule.top_toSubmodule]
    exact Submodule.mem_top
  have himg := Submodule.mem_map_of_mem
    (f := matrixCoefficientLinear (R := ℂ) (C := A) (bE.toBasis.coord i)) hv
  rw [Submodule.map_iSup] at himg
  rw [← hbE_mat, coefficientMatrix_apply, ← matrixCoefficientLinear_apply]
  suffices (⨆ W : {W : Subcomodule ℂ A (EuclideanSpace ℂ (Fin n)) | IsAtom W},
      W.1.toSubmodule.map (matrixCoefficientLinear (R := ℂ) (C := A) (bE.toBasis.coord i))) ≤
      sSup (simpleUnitaryCoefficientSubmodules A) from this himg
  refine iSup_le fun ⟨W, hW⟩ ↦
    (?_ : _ ≤ matrixCoefficientSubmodule (R := ℂ) (C := A) (M := W)).trans (le_sSup ?_)
  · rintro _ ⟨w, hw, rfl⟩
    have hsub : W.subtype ⟨w, hw⟩ = w := W.subtype_apply ⟨w, hw⟩
    rw [matrixCoefficientLinear_apply, ← hsub, matrixCoefficient_map]
    exact matrixCoefficient_mem_submodule _ _
  · have hWUnit : IsUnitary ℂ A W := W.isUnitary hUnit
    let _ := Comodule.convolutionModule (R := ℂ) (C := A) (M := EuclideanSpace ℂ (Fin n))
    let _ := Comodule.convolutionModule (R := ℂ) (C := A) (M := W)
    have : IsSimpleModule (WithConv (A →ₗ[ℂ] ℂ)) W :=
      W.isSimpleModule_convolution_iff_isAtom.mpr hW
    have : IsSimpleOrder (Subcomodule ℂ A W) := isSimpleModule_convolution_iff.mp inferInstance
    let m := Module.finrank ℂ W
    let bW : OrthonormalBasis (Fin m) ℂ W := stdOrthonormalBasis ℂ W
    let eW : W ≃ₗ[ℂ] (Fin m → ℂ) := bW.toBasis.equivFun
    let _ : Comodule ℂ A (Fin m → ℂ) := Comodule.Transport eW
    have : IsSimpleOrder (Subcomodule ℂ A (Fin m → ℂ)) :=
      (Subcomodule.transportOrderIso eW).symm.isSimpleOrder
    have hcoeff_eq : matrixCoefficientSubmodule (R := ℂ) (C := A) (M := W) =
        matrixCoefficientSubmodule (R := ℂ) (C := A) (M := Fin m → ℂ) :=
      (matrixCoefficientSubmodule_transport eW).symm
    refine ⟨hcoeff_eq ▸ finMatrix_mem_simpleCoefficientSubmodules,
      m, inferInstance, inferInstance, ?_, hcoeff_eq⟩
    rw [Comodule.coefficientMatrix_basisFun_transport_equivFun bW.toBasis]
    exact hWUnit.coefficientMatrix_mem_unitary bW

omit [StarModule ℂ A] [StarCoalgebra ℂ A] in
private theorem mem_simpleUnitaryCoefficientSubmodules_of_mem
    (hSU_span : sSup (simpleUnitaryCoefficientSubmodules A) = ⊤)
    {Q : Submodule ℂ A} (hQ : Q ∈ simpleCoefficientSubmodules ℂ A) :
    Q ∈ simpleUnitaryCoefficientSubmodules A := by
  by_contra hQnot
  have hsub : simpleUnitaryCoefficientSubmodules A ⊆ simpleCoefficientSubmodules ℂ A \ {Q} :=
    fun P hP ↦ ⟨hP.1, fun hPQ ↦ hQnot (Set.mem_singleton_iff.mp hPQ ▸ hP)⟩
  have htop : sSup (simpleCoefficientSubmodules ℂ A \ {Q}) = ⊤ :=
    top_unique (hSU_span ▸ sSup_le_sSup hsub)
  have hdisj := sSupIndep_simpleCoefficientSubmodules hQ
  rw [htop] at hdisj
  exact bot_notMem_simpleCoefficientSubmodules ((by simpa using hdisj.eq_bot : Q = ⊥) ▸ hQ)

/-- If the matrix entries of finite-dimensional unitary comodules span a complex Hopf star algebra
`A`, then `A` admits an `AlgebraicHaar` functional. -/
theorem nonempty_algebraicHaar_of_span_unitaryCoefficientSet_eq_top
    (hspan : Submodule.span ℂ (unitaryCoefficientSet A) = ⊤) :
    Nonempty (AlgebraicHaar A) := by
  classical
  have hSU_span := sSup_simpleUnitaryCoefficientSubmodules_eq_top hspan
  have hSimpleSpan : sSup (simpleCoefficientSubmodules ℂ A) = ⊤ :=
    top_unique (hSU_span ▸ sSup_le_sSup fun _ hP ↦ hP.1)
  let h := sweedlerIntegral hSimpleSpan
  have hl : h.IsLeftInvariantIntegral := isLeftInvariantIntegral_sweedlerIntegral hSimpleSpan
  have hr : h.IsRightInvariantIntegral := isRightInvariantIntegral_sweedlerIntegral hSimpleSpan
  have h1 : h 1 = 1 := sweedlerIntegral_one hSimpleSpan
  choose mP ρP hSimpleP hUnitP hEqP using fun P : simpleCoefficientSubmodules ℂ A ↦
    (mem_simpleUnitaryCoefficientSubmodules_of_mem hSU_span P.2).2
  let conjSubmodule (P : simpleCoefficientSubmodules ℂ A) : Submodule ℂ A :=
    letI : Comodule ℂ A (Fin (mP P) → ℂ) := ρP P
    letI : Comodule ℂ A (Fin (mP P) → ℂ) :=
      conjugateMatrixComodule (A := A) (Pi.basisFun ℂ (Fin (mP P)))
    matrixCoefficientSubmodule (R := ℂ) (C := A) (M := Fin (mP P) → ℂ)
  have hPbar_mem (P : simpleCoefficientSubmodules ℂ A) :
      conjSubmodule P ∈ simpleCoefficientSubmodules ℂ A := by
    let _ := ρP P
    have := hSimpleP P
    exact conjFinMatrix_mem_simpleCoefficientSubmodules
  have hDiag (P : simpleCoefficientSubmodules ℂ A) {x : A} (hx : x ∈ P.1) :
      0 ≤ h (star x * x) := by
    let Pbar : simpleCoefficientSubmodules ℂ A := ⟨conjSubmodule P, hPbar_mem P⟩
    let _ := ρP P
    have := hSimpleP P
    let _ := ρP Pbar
    have := hSimpleP Pbar
    exact map_star_mul_self_nonneg_of_conj_unitary hl hr h1
      (Pi.basisFun ℂ (Fin (mP P))) (hUnitP P) (Pi.basisFun ℂ (Fin (mP Pbar))) (hUnitP Pbar)
      (hEqP Pbar) (hEqP P ▸ hx)
  have hCross {P Q : simpleCoefficientSubmodules ℂ A} (hPQ : P ≠ Q)
      {x y : A} (hx : x ∈ P.1) (hy : y ∈ Q.1) : h (star x * y) = 0 := by
    let _ := ρP P
    have := hSimpleP P
    let _ := ρP Q
    have := hSimpleP Q
    have huP2 : coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin (mP P))) *
        (coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin (mP P))))ᴴ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp (hUnitP P)).2
    have hHom (g : Comodule.Hom ℂ A (Fin (mP Q) → ℂ) (Fin (mP P) → ℂ)) : g = 0 := by
      by_contra hg
      exact hPQ <| Subtype.ext <| (hEqP P).trans <|
        (matrixCoefficientSubmodule_eq_of_ne_zero hg).symm.trans (hEqP Q).symm
    exact hr.map_star_mul_eq_zero_of_mem_matrixCoefficientSubmodule
      (Pi.basisFun ℂ (Fin (mP P))) (Pi.basisFun ℂ (Fin (mP Q))) huP2 hHom
      (hEqP P ▸ hx) (hEqP Q ▸ hy)
  refine ⟨⟨h, h1, hl, hr, fun a ↦ ?_⟩⟩
  obtain ⟨d, rfl⟩ :=
    (Comodule.isInternal_of_sSup_simpleCoefficientSubmodules_eq_top hSimpleSpan).2 a
  have ha : DirectSum.coeAddMonoidHom
      (fun P : simpleCoefficientSubmodules ℂ A ↦ (P.1 : Submodule ℂ A)) d =
      ∑ P ∈ d.support, (d P : A) := by
    conv_lhs => rw [← DirectSum.sum_support_of d]
    simp [map_sum]
  rw [ha, star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum, map_sum]
  refine Finset.sum_nonneg fun P _ ↦ ?_
  rw [Finset.sum_eq_single P (fun Q _ hQP ↦ hCross hQP.symm (d P).2 (d Q).2)
    (fun hPnot ↦ by simp [DFinsupp.notMem_support_iff.mp hPnot])]
  exact hDiag P (d P).2

/-- **Dijkhuizen–Koornwinder compact-type equivalence.** A complex Hopf star algebra admits an
algebraic Haar functional if and only if the matrix entries of its finite-dimensional unitary
comodules span the algebra over `ℂ`. -/
theorem compactType_iff :
    Nonempty (AlgebraicHaar A) ↔ Submodule.span ℂ (unitaryCoefficientSet A) = ⊤ :=
  ⟨fun ⟨h⟩ ↦ h.span_unitaryCoefficientSet_eq_top,
    nonempty_algebraicHaar_of_span_unitaryCoefficientSet_eq_top⟩

end HopfStarAlgebra

end CompactType

end TauCeti
