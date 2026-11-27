/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Prod
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Orthogonal relevant pairs and framed complements

Given quadratic spaces `(W, Q_W)` and `(V, Q_V)` over a field `K` of characteristic not two, a
*relevant pair* of hyperbolic index `j` consists of an isometric embedding `W →qᵢ Q_V` with
nondegenerate domain whose orthogonal complement `W^⊥` is isometric to `H^j ⊥ ⟨c⟩` for some
nonzero scalar `c ∈ Kˣ`, where `H^j` is the orthogonal sum of `j` hyperbolic planes. A *framed*
orthogonal relevant pair equips this datum with a chosen scalar `c` and an explicit isometric
equivalence `W^⊥ ≃qᵢ H^j ⊥ ⟨c⟩`, distinguishing an anisotropic line generator.

Because `W` is nondegenerate and finite-dimensional, `V` decomposes orthogonally as `W ⊥ W^⊥`,
so `V` is itself finite-dimensional and nondegenerate of dimension `dim W + 2j + 1`, and the
special orthogonal group `SO(Q_W)` embeds into `SO(Q_V)` by acting trivially on `W^⊥`. Transport
along isometries of `W` and `V` intertwines these stabilizer embeddings, and scalar extension to
a field extension `L / K` preserves both the framed datum and the stabilizer embedding.

## Main definitions

* `TauCeti.hyperbolicSum R j`: the orthogonal sum of `j` copies of the hyperbolic plane
  `⟨1, -1⟩`.
* `TauCeti.OrthogonalRelevantPair Q_W Q_V j`: an isometric embedding `W →qᵢ Q_V` with
  nondegenerate domain whose orthogonal complement is isometric to `H^j ⊥ ⟨c⟩`.
* `TauCeti.FramedOrthogonalRelevantPair Q_W Q_V j`: an orthogonal relevant pair equipped with a
  chosen unit `lineCoeff : Kˣ` and an explicit framing `W^⊥ ≃qᵢ H^j ⊥ ⟨lineCoeff⟩`.
* `TauCeti.OrthogonalRelevantPair.stabilizerHom`: the stabilizer embedding `SO(Q_W) →* SO(Q_V)`
  acting as the identity on `W^⊥`.
* `TauCeti.OrthogonalRelevantPair.map`, `TauCeti.FramedOrthogonalRelevantPair.map`: transport along
  isometric equivalences.
* `TauCeti.OrthogonalRelevantPair.baseChange`, `TauCeti.FramedOrthogonalRelevantPair.baseChange`:
  extension of scalars to a field extension.
* `TauCeti.FramedOrthogonalRelevantPair.ofProd`: the canonical framed relevant pair on the
  orthogonal sum `Q_W ⊥ (H^j ⊥ ⟨c⟩)`.

## Main results

* `TauCeti.nondegenerate_hyperbolicSum`: `hyperbolicSum R j` is nondegenerate.
* `TauCeti.OrthogonalRelevantPair.finrank_eq`, `TauCeti.OrthogonalRelevantPair.odd_codimension`:
  the ambient dimension satisfies `dim V = dim W + 2j + 1`, so `dim V - dim W` is odd.
* `TauCeti.OrthogonalRelevantPair.stabilizerHom_injective`,
  `TauCeti.OrthogonalRelevantPair.mem_range_stabilizerHom_iff`: `stabilizerHom` is injective, with
  image the subgroup of `SO(Q_V)` fixing `W^⊥` pointwise.
* `TauCeti.OrthogonalRelevantPair.stabilizerHom_specialOrthogonalGroupCongr`: any intertwining pair
  of isometries intertwines the stabilizer embeddings.
* `TauCeti.OrthogonalRelevantPair.stabilizerHom_baseChange`: `stabilizerHom` commutes with
  `TauCeti.QuadraticMap.specialOrthogonalGroupBaseChange`.

## References

* D. Jiang and L. Zhang, *Arthur parameters and cuspidal automorphic modules of classical groups*,
  Ann. of Math. 191 (2020), §2.1 and §2.4.
* W. T. Gan, B. H. Gross, and D. Prasad, *Symplectic local root numbers, central critical
  `L` values, and restriction problems in the representation theory of classical groups*,
  Astérisque 346 (2012), §2 and §12.
-/

public section

open Module QuadraticMap QuadraticForm TauCeti.QuadraticMap

open scoped TensorProduct

namespace TauCeti

/-! ### Split hyperbolic sums and base change -/

section HyperbolicSum

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The orthogonal sum of `j` copies of the hyperbolic plane `⟨1, -1⟩` over a commutative ring
in which two is invertible. -/
def hyperbolicSum (R : Type*) [CommRing R] [_i2 : Invertible (2 : R)] (j : ℕ) :
    QuadraticForm R (Fin j → Fin 2 → R) :=
  QuadraticMap.pi fun _ : Fin j ↦ hyperbolicPlane R

/-- Evaluation of `hyperbolicSum` in its coordinate pairs. -/
@[simp]
theorem hyperbolicSum_apply (j : ℕ) (x : Fin j → Fin 2 → R) :
    hyperbolicSum R j x = ∑ i : Fin j, (x i 0 ^ 2 - x i 1 ^ 2) := by
  simp [hyperbolicSum]

/-- The polar form of `hyperbolicSum` in its coordinate pairs. -/
@[simp]
theorem polar_hyperbolicSum (j : ℕ) (x y : Fin j → Fin 2 → R) :
    polar (hyperbolicSum R j) x y = 2 * ∑ i : Fin j, (x i 0 * y i 0 - x i 1 * y i 1) := by
  simp only [QuadraticMap.polar, hyperbolicSum_apply, Pi.add_apply, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- The zero-fold hyperbolic sum is the zero quadratic form. -/
@[simp]
theorem hyperbolicSum_zero : hyperbolicSum R 0 = 0 := by
  ext x
  simp

/-- The split hyperbolic sum `hyperbolicSum R j` is nondegenerate when two is invertible. -/
theorem nondegenerate_hyperbolicSum (j : ℕ) : (hyperbolicSum R j).Nondegenerate :=
  nondegenerate_polar_iff.mp <|
    QuadraticMap.nondegenerate_polarBilin_pi_iff.mpr fun _ ↦
      nondegenerate_polar_iff.mpr nondegenerate_hyperbolicPlane

/-- Peeling off the first hyperbolic plane from `hyperbolicSum R (j + 1)`. -/
def hyperbolicSumSuccIsometryEquiv (j : ℕ) :
    ((hyperbolicPlane R).prod (hyperbolicSum R j)).IsometryEquiv (hyperbolicSum R (j + 1)) :=
  QuadraticMap.IsometryEquiv.consPi fun _ : Fin (j + 1) ↦ hyperbolicPlane R

@[simp]
theorem hyperbolicSumSuccIsometryEquiv_apply (j : ℕ) (x : Fin 2 → R)
    (y : Fin j → Fin 2 → R) :
    hyperbolicSumSuccIsometryEquiv (R := R) j (x, y) = Fin.cons x y := by
  dsimp only [hyperbolicSumSuccIsometryEquiv]
  exact QuadraticMap.IsometryEquiv.consPi_apply (fun _ : Fin (j + 1) ↦ hyperbolicPlane R) x y

/-- Identifying `hyperbolicSum R j` with a diagonal weighted sum of squares on `Fin j × Fin 2`. -/
def hyperbolicSumEquivWeightedSumSquares (j : ℕ) :
    (hyperbolicSum R j).IsometryEquiv
      (weightedSumSquares R fun p : Fin j × Fin 2 ↦ if p.2 = 0 then (1 : R) else -1) where
  toLinearEquiv :=
    { toFun x p := x p.1 p.2
      invFun y i k := y (i, k)
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_app' x := by
    rw [weightedSumSquares_apply, hyperbolicSum_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [Fin.sum_univ_two, pow_two, sub_eq_add_neg]

@[simp]
theorem hyperbolicSumEquivWeightedSumSquares_apply (j : ℕ)
    (x : Fin j → Fin 2 → R) (p : Fin j × Fin 2) :
    hyperbolicSumEquivWeightedSumSquares (R := R) j x p = x p.1 p.2 :=
  (rfl)

@[simp]
theorem hyperbolicSumEquivWeightedSumSquares_symm_apply (j : ℕ)
    (y : Fin j × Fin 2 → R) (i : Fin j) (k : Fin 2) :
    (hyperbolicSumEquivWeightedSumSquares (R := R) j).symm y i k = y (i, k) :=
  (rfl)

private def weightedSumSquaresIndicatorEquiv (R : Type*) [CommRing R] (A : Type*)
    [CommRing A] [Algebra R A] (j : ℕ) :
    (weightedSumSquares A fun p : Fin j × Fin 2 ↦
        algebraMap R A (if p.2 = 0 then (1 : R) else -1)).IsometryEquiv
      (weightedSumSquares A fun p : Fin j × Fin 2 ↦ if p.2 = 0 then (1 : A) else -1) where
  toLinearEquiv := LinearEquiv.refl A (Fin j × Fin 2 → A)
  map_app' x := by
    simp only [weightedSumSquares_apply]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    split_ifs <;> simp

/-- Base change carries `hyperbolicSum R j` to `hyperbolicSum A j`. -/
noncomputable def baseChangeHyperbolicSum (j : ℕ) (A : Type*) [CommRing A] [Algebra R A]
    [Invertible (2 : A)] :
    ((hyperbolicSum R j).baseChange A).IsometryEquiv (hyperbolicSum A j) :=
  ((hyperbolicSumEquivWeightedSumSquares (R := R) j).baseChange A).trans
    ((QuadraticForm.baseChangeWeightedSumSquares (A := A)
        (fun p : Fin j × Fin 2 ↦ if p.2 = 0 then (1 : R) else -1)).trans
      ((weightedSumSquaresIndicatorEquiv R A j).trans
        (hyperbolicSumEquivWeightedSumSquares (R := A) j).symm))

@[simp]
theorem baseChangeHyperbolicSum_tmul (j : ℕ) (A : Type*) [CommRing A] [Algebra R A]
    [Invertible (2 : A)] (a : A) (x : Fin j → Fin 2 → R) (i : Fin j) (k : Fin 2) :
    baseChangeHyperbolicSum (R := R) j A (a ⊗ₜ x) i k = x i k • a := by
  have h1 :
      baseChangeHyperbolicSum (R := R) j A (a ⊗ₜ x) i k =
        (hyperbolicSumEquivWeightedSumSquares (R := A) j).symm
          (QuadraticForm.baseChangeWeightedSumSquares (A := A)
            (fun p : Fin j × Fin 2 ↦ if p.2 = 0 then (1 : R) else -1)
            ((hyperbolicSumEquivWeightedSumSquares (R := R) j).baseChange A
              (a ⊗ₜ x))) i k :=
    rfl
  rw [h1, QuadraticMap.IsometryEquiv.baseChange_tmul,
    QuadraticForm.baseChangeWeightedSumSquares_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

/-- Base change carries a rank-one diagonal form `c • sq` to `algebraMap R A c • sq`. -/
def baseChangeLine (c : R) (A : Type*) [CommRing A] [Algebra R A] :
    (QuadraticForm.baseChange A (c • (QuadraticMap.sq : QuadraticForm R R))).IsometryEquiv
      (algebraMap R A c • (QuadraticMap.sq : QuadraticForm A A)) where
  toLinearEquiv := TensorProduct.AlgebraTensorModule.rid R A A
  map_app' x := by
    have h : (algebraMap R A c • (QuadraticMap.sq : QuadraticForm A A)).comp
          (TensorProduct.AlgebraTensorModule.rid R A A).toLinearMap =
        QuadraticForm.baseChange A (c • (QuadraticMap.sq : QuadraticForm R R)) := by
      apply baseChange_ext
      intro r
      simp [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
    exact DFunLike.congr_fun h x

@[simp]
theorem baseChangeLine_tmul (c : R) (A : Type*) [CommRing A] [Algebra R A] (a : A) (r : R) :
    baseChangeLine c A (a ⊗ₜ r) = r • a :=
  TensorProduct.AlgebraTensorModule.rid_tmul A r a

end HyperbolicSum

section HyperbolicSumField

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- Over a field of characteristic not two, `hyperbolicSum K j` has class
`j • hyperbolicClass K`. -/
@[simp]
theorem formClass_hyperbolicSum (j : ℕ) :
    formClass (hyperbolicSum K j) (nondegenerate_hyperbolicSum j) = j • hyperbolicClass K := by
  induction j with
  | zero =>
    rw [zero_nsmul, formClass_eq_zero_iff]
    exact Module.finrank_zero_of_subsingleton
  | succ j ih =>
    have heq :=
      (formClass_eq_iff (hyperbolicSum K (j + 1)) (nondegenerate_hyperbolicSum (j + 1))
        ((hyperbolicPlane K).prod (hyperbolicSum K j))
        (nondegenerate_hyperbolicPlane.prod (nondegenerate_hyperbolicSum j))).mpr
        ⟨(hyperbolicSumSuccIsometryEquiv (R := K) j).symm⟩
    rw [heq,
      formClass_prod _ nondegenerate_hyperbolicPlane _ (nondegenerate_hyperbolicSum j),
      formClass_hyperbolicPlane, ih, succ_nsmul']

end HyperbolicSumField

/-! ### Orthogonal relevant pairs and framed complements -/

/-- An unframed *orthogonal relevant pair* of hyperbolic index `j` from `(W, Q_W)` to `(V, Q_V)`:
an isometric embedding `embed : Q_W →qᵢ Q_V` with nondegenerate domain `Q_W` whose orthogonal
complement in `V` is isometric to `H^j ⊥ ⟨c⟩` for some nonzero scalar `c`. -/
@[ext]
structure OrthogonalRelevantPair {K : Type*} [Field K] [Invertible (2 : K)]
    {W V : Type*} [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]
    (Q_W : QuadraticForm K W) (Q_V : QuadraticForm K V) (j : ℕ) where
  /-- The underlying isometric embedding `W →qᵢ V`. -/
  embed : Q_W →qᵢ Q_V
  /-- Nondegeneracy of the domain quadratic form `Q_W`. -/
  nondegenerate_domain : Q_W.Nondegenerate
  /-- Existence of an anisotropic scalar `c` framing the orthogonal complement as
  `H^j ⊥ ⟨c⟩`. -/
  exists_complement :
    ∃ c : Kˣ, Nonempty ((Q_V.restrict
      (LinearMap.BilinForm.orthogonal Q_V.polarBilin
        (LinearMap.range embed.toLinearMap))).IsometryEquiv
      ((hyperbolicSum K j).prod ((c : K) • QuadraticMap.sq)))

/-- A *framed orthogonal relevant pair* of hyperbolic index `j` from `(W, Q_W)` to `(V, Q_V)`:
an isometric embedding `embed : Q_W →qᵢ Q_V` with nondegenerate domain, together with a chosen
unit `lineCoeff : Kˣ` and an explicit isometric equivalence from `W^⊥` onto
`H^j ⊥ ⟨lineCoeff⟩`. -/
structure FramedOrthogonalRelevantPair {K : Type*} [Field K] [Invertible (2 : K)]
    {W V : Type*} [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]
    (Q_W : QuadraticForm K W) (Q_V : QuadraticForm K V) (j : ℕ) where
  /-- The underlying isometric embedding `W →qᵢ V`. -/
  embed : Q_W →qᵢ Q_V
  /-- Nondegeneracy of the domain quadratic form `Q_W`. -/
  nondegenerate_domain : Q_W.Nondegenerate
  /-- The quadratic value of the distinguished anisotropic line generator in `W^⊥`. -/
  lineCoeff : Kˣ
  /-- The explicit framing isomorphism `W^⊥ ≃qᵢ H^j ⊥ ⟨lineCoeff⟩`. -/
  complementEquiv :
    (Q_V.restrict
      (LinearMap.BilinForm.orthogonal Q_V.polarBilin
        (LinearMap.range embed.toLinearMap))).IsometryEquiv
      ((hyperbolicSum K j).prod ((lineCoeff : K) • QuadraticMap.sq))

namespace FramedOrthogonalRelevantPair

section Forget

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V : Type*} [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V} {j : ℕ}

/-- Forget the framing of a framed orthogonal relevant pair, keeping only the isometric embedding
and the odd-dimensional hyperbolic-plus-line complement condition. -/
def toOrthogonalRelevantPair (F : FramedOrthogonalRelevantPair Q_W Q_V j) :
    OrthogonalRelevantPair Q_W Q_V j where
  embed := F.embed
  nondegenerate_domain := F.nondegenerate_domain
  exists_complement := ⟨F.lineCoeff, ⟨F.complementEquiv⟩⟩

@[simp]
theorem toOrthogonalRelevantPair_embed (F : FramedOrthogonalRelevantPair Q_W Q_V j) :
    F.toOrthogonalRelevantPair.embed = F.embed :=
  (rfl)

/-- Two framed relevant pairs agree if and only if they share the same isometric embedding and their
inverse framing maps take the same values in `V`. (The scalar `lineCoeff` is then forced by the
quadratic value at `(0, 1)`.) -/
@[ext (iff := false)]
theorem ext {F₁ F₂ : FramedOrthogonalRelevantPair Q_W Q_V j}
    (hembed : F₁.embed = F₂.embed)
    (hframe : ∀ y : (Fin j → Fin 2 → K) × K,
      (F₁.complementEquiv.symm y : V) = (F₂.complementEquiv.symm y : V)) :
    F₁ = F₂ := by
  have hcVal : (F₁.lineCoeff : K) = (F₂.lineCoeff : K) := by
    have h1 := F₁.complementEquiv.symm.map_app (0, (1 : K))
    have h2 := F₂.complementEquiv.symm.map_app (0, (1 : K))
    rw [QuadraticMap.restrict_apply, hframe (0, 1)] at h1
    rw [QuadraticMap.restrict_apply] at h2
    have h1' : Q_V (F₂.complementEquiv.symm (0, (1 : K)) : V) = F₁.lineCoeff := by
      simpa using h1
    have h2' : Q_V (F₂.complementEquiv.symm (0, (1 : K)) : V) = F₂.lineCoeff := by
      simpa using h2
    exact h1'.symm.trans h2'
  have hc : F₁.lineCoeff = F₂.lineCoeff := Units.ext hcVal
  rcases F₁ with ⟨embed₁, hnd₁, c₁, f₁⟩
  rcases F₂ with ⟨embed₂, hnd₂, c₂, f₂⟩
  dsimp at hembed hc
  subst hembed hc
  congr 1
  rw [← f₁.symm_symm, ← f₂.symm_symm]
  congr 1
  exact DFunLike.ext _ _ fun y ↦ Subtype.ext (hframe y)

end Forget

end FramedOrthogonalRelevantPair

/-! ### Orthogonal complement geometry and ambient splitting -/

namespace OrthogonalRelevantPair

section Basic

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V : Type*} [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V} {j : ℕ}
  (P : OrthogonalRelevantPair Q_W Q_V j)

/-- The polar orthogonal complement `W^⊥` of the embedded subspace in `V`. -/
abbrev orthogonal : Submodule K V :=
  LinearMap.BilinForm.orthogonal Q_V.polarBilin (LinearMap.range P.embed.toLinearMap)

theorem mem_orthogonal_iff {v : V} :
    v ∈ P.orthogonal ↔ ∀ w : W, polar Q_V (P.embed w) v = 0 := by
  simp [orthogonal, LinearMap.BilinForm.mem_orthogonal_iff]

/-- The underlying isometric embedding of a relevant pair is injective. -/
theorem embed_injective : Function.Injective P.embed :=
  P.embed.injective_of_radical_eq_bot P.nondegenerate_domain.radical_eq_bot

/-- The canonical isometric equivalence from `Q_W` to the restriction of `Q_V` to `range embed`. -/
noncomputable def domainRangeEquiv :
    Q_W.IsometryEquiv (Q_V.restrict (LinearMap.range P.embed.toLinearMap)) where
  toLinearEquiv := LinearEquiv.ofInjective P.embed.toLinearMap P.embed_injective
  map_app' w := P.embed.map_app w

@[simp]
theorem coe_domainRangeEquiv_apply (w : W) :
    (P.domainRangeEquiv w : V) = P.embed w :=
  (rfl)

@[simp]
theorem domainRangeEquiv_symm_embed (w : W) :
    P.domainRangeEquiv.symm ⟨P.embed w, ⟨w, rfl⟩⟩ = w :=
  P.domainRangeEquiv.symm_apply_apply w

/-- The restriction of `Q_V` to the image of `embed` is nondegenerate. -/
theorem nondegenerate_restrict_range :
    (Q_V.restrict (LinearMap.range P.embed.toLinearMap)).Nondegenerate :=
  P.domainRangeEquiv.nondegenerate_iff.mp P.nondegenerate_domain

/-- The orthogonal complement `W^⊥` is finite-dimensional of dimension `2j + 1`. -/
theorem finiteDimensional_orthogonal : FiniteDimensional K P.orthogonal := by
  obtain ⟨c, ⟨e⟩⟩ := P.exists_complement
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- The restriction of `Q_V` to `W^⊥` is nondegenerate. -/
theorem nondegenerate_restrict_orthogonal : (Q_V.restrict P.orthogonal).Nondegenerate := by
  obtain ⟨c, ⟨e⟩⟩ := P.exists_complement
  refine e.nondegenerate_iff.mpr ?_
  have hsq : (QuadraticMap.sq : QuadraticForm K K).Nondegenerate := by
    rw [← nondegenerate_polar_iff, LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (QuadraticMap.sq : QuadraticForm K K).isRefl_polarBilin]
    intro x hx
    have h1 := hx 1
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, QuadraticMap.sq_apply,
      mul_one] at h1
    have h2 : 2 * x = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (Invertible.ne_zero (2 : K))
  exact (nondegenerate_hyperbolicSum j).prod
    ((QuadraticMap.nondegenerate_smul_iff c.isUnit _).mpr hsq)

/-- The dimension of the orthogonal complement `W^⊥` is `2j + 1`. -/
theorem finrank_orthogonal : Module.finrank K P.orthogonal = 2 * j + 1 := by
  obtain ⟨c, ⟨e⟩⟩ := P.exists_complement
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_pi_fintype,
    Module.finrank_self]
  simp
  ring

end Basic

section Splitting

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup V] [Module K V]
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V} {j : ℕ}
  (P : OrthogonalRelevantPair Q_W Q_V j)

/-- For a finite-dimensional domain `W`, `range embed` and `W^⊥` are complementary in `V`. -/
theorem isCompl_orthogonal : IsCompl (LinearMap.range P.embed.toLinearMap) P.orthogonal := by
  have : FiniteDimensional K (LinearMap.range P.embed.toLinearMap) :=
    Module.Finite.equiv P.domainRangeEquiv.toLinearEquiv
  exact P.nondegenerate_restrict_range.isCompl_orthogonal

/-- The orthogonal splitting `Q_W ⊥ Q_V|_{W^⊥} ≃qᵢ Q_V` determined by a relevant pair. -/
noncomputable def ambientIsometryEquiv :
    (Q_W.prod (Q_V.restrict P.orthogonal)).IsometryEquiv Q_V :=
  (P.domainRangeEquiv.prod (IsometryEquiv.refl (Q_V.restrict P.orthogonal))).trans
    (IsometryEquiv.prodRestrictOrthogonal Q_V (LinearMap.range P.embed.toLinearMap)
      P.isCompl_orthogonal)

@[simp]
theorem ambientIsometryEquiv_apply (x : W × P.orthogonal) :
    P.ambientIsometryEquiv x = P.embed x.1 + x.2 := by
  simp [ambientIsometryEquiv]

@[simp]
theorem ambientIsometryEquiv_symm_embed (w : W) :
    P.ambientIsometryEquiv.symm (P.embed w) = (w, 0) :=
  P.ambientIsometryEquiv.symm_apply_eq.mpr (by simp)

@[simp]
theorem ambientIsometryEquiv_symm_of_mem_orthogonal (u : P.orthogonal) :
    P.ambientIsometryEquiv.symm u = (0, u) :=
  P.ambientIsometryEquiv.symm_apply_eq.mpr (by simp)

include P in
/-- The ambient space `V` of a relevant pair with finite-dimensional domain `W` is
finite-dimensional. -/
theorem finiteDimensional_codomain : FiniteDimensional K V := by
  have := P.finiteDimensional_orthogonal
  exact Module.Finite.equiv P.ambientIsometryEquiv.toLinearEquiv

include P in
/-- The ambient quadratic form `Q_V` of a relevant pair is nondegenerate. -/
theorem nondegenerate_codomain : Q_V.Nondegenerate :=
  P.ambientIsometryEquiv.nondegenerate_iff.mp
    (P.nondegenerate_domain.prod P.nondegenerate_restrict_orthogonal)

include P in
/-- The ambient dimension satisfies `dim V = dim W + 2j + 1`. -/
theorem finrank_eq :
    Module.finrank K V = Module.finrank K W + 2 * j + 1 := by
  have := P.finiteDimensional_orthogonal
  rw [← P.ambientIsometryEquiv.toLinearEquiv.finrank_eq, Module.finrank_prod,
    P.finrank_orthogonal, add_assoc]

include P in
/-- The codimension `dim V - dim W` of a relevant pair is odd. -/
theorem odd_codimension : (Module.finrank K V - Module.finrank K W) % 2 = 1 := by
  rw [P.finrank_eq, add_assoc, Nat.add_sub_cancel_left]
  omega

include P in
/-- The ambient form `Q_V` is isometric to `Q_W ⊥ H^j ⊥ ⟨c⟩` for some nonzero scalar `c`. -/
theorem exists_equivalent_prod :
    ∃ c : Kˣ,
      Q_V.Equivalent (Q_W.prod ((hyperbolicSum K j).prod ((c : K) • QuadraticMap.sq))) := by
  obtain ⟨c, ⟨e⟩⟩ := P.exists_complement
  exact ⟨c, ⟨P.ambientIsometryEquiv.symm.trans ((IsometryEquiv.refl Q_W).prod e)⟩⟩

end Splitting

end OrthogonalRelevantPair

/-! ### Framing accessors -/

namespace FramedOrthogonalRelevantPair

section Basic

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V : Type*} [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V} {j : ℕ}
  (F : FramedOrthogonalRelevantPair Q_W Q_V j)

/-- The polar orthogonal complement `W^⊥` of a framed relevant pair. -/
abbrev orthogonal : Submodule K V := F.toOrthogonalRelevantPair.orthogonal

/-- The distinguished anisotropic vector in `W^⊥` corresponding to `(0, 1)` under the framing. -/
noncomputable def lineVector : V := (F.complementEquiv.symm (0, 1) : V)

theorem lineVector_mem_orthogonal : F.lineVector ∈ F.orthogonal :=
  (F.complementEquiv.symm (0, 1)).property

@[simp]
theorem apply_lineVector : Q_V F.lineVector = F.lineCoeff := by
  have h := F.complementEquiv.symm.map_app (0, (1 : K))
  rw [QuadraticMap.restrict_apply] at h
  simpa [lineVector] using h

theorem apply_lineVector_ne_zero : Q_V F.lineVector ≠ 0 := by
  rw [F.apply_lineVector]
  exact F.lineCoeff.ne_zero

theorem lineVector_ne_zero : F.lineVector ≠ 0 :=
  fun h ↦ F.apply_lineVector_ne_zero (by rw [h, map_zero])

/-- The isometric embedding of the split hyperbolic space `H^j` into `V` provided by the
framing. -/
noncomputable def hyperbolicMap : hyperbolicSum K j →qᵢ Q_V where
  toLinearMap :=
    (LinearMap.BilinForm.orthogonal Q_V.polarBilin
        (LinearMap.range F.embed.toLinearMap)).subtype.comp
      (F.complementEquiv.symm.toLinearMap.comp (LinearMap.inl K (Fin j → Fin 2 → K) K))
  map_app' x := by
    have h := F.complementEquiv.symm.map_app (x, (0 : K))
    rw [QuadraticMap.restrict_apply] at h
    -- Expose the coercion of the composite linear map to the inverse framing value.
    change Q_V (F.complementEquiv.symm (x, 0) : V) = hyperbolicSum K j x
    simpa using h

@[simp]
theorem hyperbolicMap_apply (x : Fin j → Fin 2 → K) :
    F.hyperbolicMap x = (F.complementEquiv.symm (x, 0) : V) :=
  (rfl)

theorem hyperbolicMap_mem_orthogonal (x : Fin j → Fin 2 → K) :
    F.hyperbolicMap x ∈ F.orthogonal :=
  (F.complementEquiv.symm (x, 0)).property

/-- Vectors in the framed hyperbolic summand are orthogonal to the distinguished line generator. -/
theorem polar_hyperbolicMap_lineVector (x : Fin j → Fin 2 → K) :
    polar Q_V (F.hyperbolicMap x) F.lineVector = 0 := by
  have h := F.complementEquiv.symm.polar_apply (x, (0 : K)) (0, (1 : K))
  have hr : polar ((hyperbolicSum K j).prod ((F.lineCoeff : K) • QuadraticMap.sq))
      (x, (0 : K)) (0, (1 : K)) = 0 := by
    simp [QuadraticMap.polar]
  rw [hr, ← QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_restrict,
    LinearMap.domRestrict₁₂_apply, QuadraticMap.polarBilin_apply_apply] at h
  exact h

/-- The ambient isometric decomposition `Q_W ⊥ H^j ⊥ ⟨lineCoeff⟩ ≃qᵢ Q_V` of a framed
pair. -/
noncomputable def ambientIsometryEquiv [FiniteDimensional K W] :
    (Q_W.prod
        ((hyperbolicSum K j).prod ((F.lineCoeff : K) • QuadraticMap.sq))).IsometryEquiv
      Q_V :=
  ((IsometryEquiv.refl Q_W).prod F.complementEquiv.symm).trans
    F.toOrthogonalRelevantPair.ambientIsometryEquiv

@[simp]
theorem ambientIsometryEquiv_apply [FiniteDimensional K W]
    (x : W × (Fin j → Fin 2 → K) × K) :
    F.ambientIsometryEquiv x = F.embed x.1 + (F.complementEquiv.symm x.2 : V) := by
  dsimp only [ambientIsometryEquiv]
  exact F.toOrthogonalRelevantPair.ambientIsometryEquiv_apply (x.1, F.complementEquiv.symm x.2)

@[simp]
theorem ambientIsometryEquiv_symm_embed [FiniteDimensional K W] (w : W) :
    F.ambientIsometryEquiv.symm (F.embed w) = (w, (0, 0)) :=
  F.ambientIsometryEquiv.symm_apply_eq.mpr (by simp)

@[simp]
theorem ambientIsometryEquiv_symm_lineVector [FiniteDimensional K W] :
    F.ambientIsometryEquiv.symm F.lineVector = (0, (0, 1)) :=
  F.ambientIsometryEquiv.symm_apply_eq.mpr (by simp [lineVector])

end Basic

end FramedOrthogonalRelevantPair

/-! ### Stabilizer embedding `SO(Q_W) →* SO(Q_V)` -/

namespace OrthogonalRelevantPair

section Stabilizer

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup V] [Module K V]
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V} {j : ℕ}
  (P : OrthogonalRelevantPair Q_W Q_V j)

/-- The stabilizer embedding `SO(Q_W) →* SO(Q_V)`, extending an element of `SO(Q_W)` by the
identity on the orthogonal complement `W^⊥`. -/
noncomputable def stabilizerHom :
    specialOrthogonalGroup Q_W →* specialOrthogonalGroup Q_V :=
  have := P.finiteDimensional_orthogonal
  (P.ambientIsometryEquiv.specialOrthogonalGroupCongr :
      specialOrthogonalGroup (Q_W.prod (Q_V.restrict P.orthogonal)) →*
        specialOrthogonalGroup Q_V).comp
    ((specialOrthogonalGroupProd Q_W (Q_V.restrict P.orthogonal)).comp
      (MonoidHom.inl (specialOrthogonalGroup Q_W)
        (specialOrthogonalGroup (Q_V.restrict P.orthogonal))))

@[simp]
theorem stabilizerHom_apply_embed (g : specialOrthogonalGroup Q_W) (w : W) :
    (P.stabilizerHom g : V ≃ₗ[K] V) (P.embed w) = P.embed ((g : W ≃ₗ[K] W) w) := by
  have := P.finiteDimensional_orthogonal
  simp [stabilizerHom, IsometryEquiv.coe_specialOrthogonalGroupCongr_apply]

@[simp]
theorem stabilizerHom_apply_of_mem_orthogonal (g : specialOrthogonalGroup Q_W)
    {v : V} (hv : v ∈ P.orthogonal) :
    (P.stabilizerHom g : V ≃ₗ[K] V) v = v := by
  have := P.finiteDimensional_orthogonal
  have hu : P.ambientIsometryEquiv.symm v = (0, ⟨v, hv⟩) :=
    P.ambientIsometryEquiv_symm_of_mem_orthogonal ⟨v, hv⟩
  simp [stabilizerHom, IsometryEquiv.coe_specialOrthogonalGroupCongr_apply, hu]

/-- The stabilizer embedding `SO(Q_W) →* SO(Q_V)` is injective. -/
theorem stabilizerHom_injective : Function.Injective P.stabilizerHom := by
  intro g₁ g₂ h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  apply P.embed_injective
  have hw := congrArg (fun f : specialOrthogonalGroup Q_V ↦ (f : V ≃ₗ[K] V) (P.embed w)) h
  simpa using hw

private theorem mem_range_embed_of_fix_orthogonal {h : specialOrthogonalGroup Q_V}
    (hfix : ∀ v ∈ P.orthogonal, (h : V ≃ₗ[K] V) v = v) (w : W) :
    (h : V ≃ₗ[K] V) (P.embed w) ∈ LinearMap.range P.embed.toLinearMap := by
  have hBnd : Q_V.polarBilin.Nondegenerate := nondegenerate_polar_iff.mpr P.nondegenerate_codomain
  have horth : (P.orthogonal).orthogonalBilin Q_V.polarBilin =
      LinearMap.range P.embed.toLinearMap :=
    LinearMap.BilinForm.orthogonal_orthogonal_of_isCompl Q_V.polarBilin
      Q_V.isSymm_polarBilin.isRefl hBnd.2 _ P.isCompl_orthogonal
  rw [← horth, Submodule.mem_orthogonalBilin]
  intro u hu
  have hpol := polar_apply_of_mem_orthogonalGroup
    (specialOrthogonalGroup_le_orthogonalGroup Q_V h.property) u (P.embed w)
  rw [hfix u hu, QuadraticMap.polar_comm Q_V u (P.embed w),
    P.mem_orthogonal_iff.mp hu w] at hpol
  simpa [QuadraticMap.polarBilin_apply_apply] using hpol

private theorem exists_specialOrthogonalGroupProd_one_of_fix
    [FiniteDimensional K P.orthogonal]
    (h' : specialOrthogonalGroup (Q_W.prod (Q_V.restrict P.orthogonal)))
    (hinvariant :
      ∀ w : W, ((h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (w, 0)).2 = 0)
    (hfix' : ∀ u : P.orthogonal,
      (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (0, u) = (0, u)) :
    ∃ g₁ : specialOrthogonalGroup Q_W,
      specialOrthogonalGroupProd Q_W (Q_V.restrict P.orthogonal) (g₁, 1) = h' := by
  have hblock2 :
      LinearMap.snd K W P.orthogonal ∘ₗ
        (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal).toLinearMap ∘ₗ
          LinearMap.inr K W P.orthogonal = LinearMap.id := by
    ext u
    simp [hfix' u]
  have hmemO :
      (⟨h', specialOrthogonalGroup_le_orthogonalGroup _ h'.property⟩ :
          orthogonalGroup (Q_W.prod (Q_V.restrict P.orthogonal))) ∈
        (orthogonalGroupProd Q_W (Q_V.restrict P.orthogonal)).range :=
    (mem_range_orthogonalGroupProd_iff Q_W (Q_V.restrict P.orthogonal)).mpr
      ⟨hinvariant, fun u ↦ by simp [hfix' u]⟩
  obtain ⟨⟨f₁, f₂⟩, hf⟩ := hmemO
  have hcoe : (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) =
      (f₁ : W ≃ₗ[K] W).prodCongr (f₂ : P.orthogonal ≃ₗ[K] P.orthogonal) := by
    have hval := (congrArg Subtype.val hf).symm
    rwa [coe_orthogonalGroupProd] at hval
  have hf₂ : (f₂ : P.orthogonal ≃ₗ[K] P.orthogonal) = LinearEquiv.refl K P.orthogonal := by
    ext u
    have hu := congrArg
      (fun φ : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal ↦ (φ (0, u)).2) hcoe
    simpa [hfix' u] using hu.symm
  have hdet : LinearEquiv.det (f₁ : W ≃ₗ[K] W) = 1 := by
    have hdet' := det_coe_specialOrthogonalGroup h'
    rw [hcoe, LinearEquiv.det_prodCongr, hf₂, LinearEquiv.det_refl, mul_one] at hdet'
    exact hdet'
  have hblock1 :
      LinearMap.fst K W P.orthogonal ∘ₗ
        (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal).toLinearMap ∘ₗ
          LinearMap.inl K W P.orthogonal = (f₁ : W ≃ₗ[K] W).toLinearMap := by
    ext w
    simp [hcoe]
  have hprod : h' ∈ (specialOrthogonalGroupProd Q_W (Q_V.restrict P.orthogonal)).range := by
    refine (mem_range_specialOrthogonalGroupProd_iff Q_W (Q_V.restrict P.orthogonal)).mpr
      ⟨hinvariant, fun u ↦ by simp [hfix' u], ?_, by simp [hblock2]⟩
    rw [hblock1, ← LinearEquiv.coe_det, hdet, Units.val_one]
  obtain ⟨⟨g₁, g₂⟩, hg⟩ := hprod
  have hg₂ : g₂ = 1 := by
    ext u
    have hu := congrArg
      (fun φ : specialOrthogonalGroup (Q_W.prod (Q_V.restrict P.orthogonal)) ↦
        ((φ : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (0, u)).2) hg
    simpa [hfix' u] using hu
  exact ⟨g₁, by simpa [hg₂] using hg⟩

/-- **Image of the stabilizer embedding.** An element of `SO(Q_V)` lies in the image of
`P.stabilizerHom` if and only if it fixes `W^⊥` pointwise. -/
theorem mem_range_stabilizerHom_iff {h : specialOrthogonalGroup Q_V} :
    h ∈ P.stabilizerHom.range ↔ ∀ v ∈ P.orthogonal, (h : V ≃ₗ[K] V) v = v := by
  constructor
  · rintro ⟨g, rfl⟩ v hv
    exact P.stabilizerHom_apply_of_mem_orthogonal g hv
  · intro hfix
    have := P.finiteDimensional_orthogonal
    set e := P.ambientIsometryEquiv
    set h' : specialOrthogonalGroup (Q_W.prod (Q_V.restrict P.orthogonal)) :=
      e.symm.specialOrthogonalGroupCongr h
    have hinvariant :
        ∀ w : W, ((h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (w, 0)).2 = 0 := by
      intro w
      obtain ⟨w', hw'⟩ := P.mem_range_embed_of_fix_orthogonal hfix w
      have heq : (h : V ≃ₗ[K] V) (e (w, 0)) = e (w', 0) := by
        simpa [e] using hw'.symm
      have h'' : (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (w, 0) = (w', 0) := by
        simp only [h']
        rw [IsometryEquiv.coe_specialOrthogonalGroupCongr_apply, IsometryEquiv.symm_symm,
          heq, e.symm_apply_apply]
      rw [h'']
    have hfix' : ∀ u : P.orthogonal,
        (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (0, u) = (0, u) := by
      intro u
      have heq : (h : V ≃ₗ[K] V) (e (0, u)) = e (0, u) := by
        simpa [e] using hfix u u.property
      simp only [h']
      rw [IsometryEquiv.coe_specialOrthogonalGroupCongr_apply, IsometryEquiv.symm_symm,
        heq, e.symm_apply_apply]
    obtain ⟨g₁, hmain⟩ := P.exists_specialOrthogonalGroupProd_one_of_fix h' hinvariant hfix'
    refine ⟨g₁, ?_⟩
    have hcongr := congrArg e.specialOrthogonalGroupCongr hmain
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv := congrArg (fun φ : specialOrthogonalGroup Q_V ↦ (φ : V ≃ₗ[K] V) v) hcongr
    simpa [stabilizerHom, h', e, IsometryEquiv.coe_specialOrthogonalGroupCongr_apply] using hv

end Stabilizer

end OrthogonalRelevantPair

namespace FramedOrthogonalRelevantPair

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup V] [Module K V]
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V} {j : ℕ}
  (F : FramedOrthogonalRelevantPair Q_W Q_V j)

/-- The stabilizer embedding `SO(Q_W) →* SO(Q_V)` of a framed relevant pair. -/
noncomputable abbrev stabilizerHom :
    specialOrthogonalGroup Q_W →* specialOrthogonalGroup Q_V :=
  F.toOrthogonalRelevantPair.stabilizerHom

@[simp]
theorem stabilizerHom_apply_lineVector (g : specialOrthogonalGroup Q_W) :
    (F.stabilizerHom g : V ≃ₗ[K] V) F.lineVector = F.lineVector :=
  F.toOrthogonalRelevantPair.stabilizerHom_apply_of_mem_orthogonal g F.lineVector_mem_orthogonal

theorem stabilizerHom_apply_hyperbolicMap (g : specialOrthogonalGroup Q_W)
    (x : Fin j → Fin 2 → K) :
    (F.stabilizerHom g : V ≃ₗ[K] V) (F.hyperbolicMap x) = F.hyperbolicMap x :=
  F.toOrthogonalRelevantPair.stabilizerHom_apply_of_mem_orthogonal g
    (F.hyperbolicMap_mem_orthogonal x)

end FramedOrthogonalRelevantPair

/-! ### Transport along isometries and intertwining of stabilizers -/

namespace OrthogonalRelevantPair

section Map

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V W' V' : Type*} [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]
  [AddCommGroup W'] [Module K W'] [AddCommGroup V'] [Module K V']
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V}
  {Q_W' : QuadraticForm K W'} {Q_V' : QuadraticForm K V'} {j : ℕ}

/-- Transport an orthogonal relevant pair along isometric equivalences of the domain and
codomain. -/
noncomputable def map (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    OrthogonalRelevantPair Q_W' Q_V' j where
  embed := e_V.toIsometry.comp (P.embed.comp e_W.symm.toIsometry)
  nondegenerate_domain := e_W.nondegenerate_iff.mp P.nondegenerate_domain
  exists_complement := by
    have hrange :
        LinearMap.range (e_V.toIsometry.comp (P.embed.comp e_W.symm.toIsometry)).toLinearMap =
          (LinearMap.range P.embed.toLinearMap).map e_V.toLinearMap := by
      ext v'
      simp only [QuadraticMap.Isometry.toLinearMap_comp, LinearMap.mem_range,
        LinearMap.comp_apply, QuadraticMap.Isometry.coe_toLinearMap, LinearEquiv.coe_toLinearMap,
        Submodule.mem_map]
      refine ⟨fun ⟨w', hw'⟩ ↦ ?_, ?_⟩
      · exact ⟨P.embed (e_W.symm w'), ⟨e_W.symm w', rfl⟩, hw'⟩
      · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
        exact ⟨e_W w, by simp⟩
    have horth :
        P.orthogonal.map e_V.toLinearMap =
          LinearMap.BilinForm.orthogonal Q_V'.polarBilin
            (LinearMap.range
              (e_V.toIsometry.comp (P.embed.comp e_W.symm.toIsometry)).toLinearMap) := by
      rw [hrange]
      exact e_V.map_orthogonal_polarBilin (LinearMap.range P.embed.toLinearMap)
    have hsub : (Q_V.restrict P.orthogonal).IsometryEquiv
        (Q_V'.restrict
          (LinearMap.BilinForm.orthogonal Q_V'.polarBilin
            (LinearMap.range
              (e_V.toIsometry.comp (P.embed.comp e_W.symm.toIsometry)).toLinearMap))) :=
      { toLinearEquiv := e_V.toLinearEquiv.ofSubmodules _ _ horth
        map_app' u := by
          -- Expose the restricted form evaluation on the submodule isomorphism.
          change Q_V' (e_V.toLinearEquiv.ofSubmodules _ _ horth u : V') = Q_V (u : V)
          rw [LinearEquiv.ofSubmodules_apply]
          exact e_V.map_app (u : V) }
    obtain ⟨c, ⟨e⟩⟩ := P.exists_complement
    exact ⟨c, ⟨hsub.symm.trans e⟩⟩

@[simp]
theorem map_embed (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') (w' : W') :
    (P.map e_W e_V).embed w' = e_V (P.embed (e_W.symm w')) :=
  (rfl)

@[simp]
theorem map_refl (P : OrthogonalRelevantPair Q_W Q_V j) :
    P.map (IsometryEquiv.refl Q_W) (IsometryEquiv.refl Q_V) = P := by
  ext w
  rfl

theorem map_trans {W'' V'' : Type*} [AddCommGroup W''] [Module K W'']
    [AddCommGroup V''] [Module K V''] {Q_W'' : QuadraticForm K W''}
    {Q_V'' : QuadraticForm K V''} (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V')
    (e_W' : Q_W'.IsometryEquiv Q_W'') (e_V' : Q_V'.IsometryEquiv Q_V'') :
    (P.map e_W e_V).map e_W' e_V' = P.map (e_W.trans e_W') (e_V.trans e_V') := by
  ext w''
  simp only [map_embed]
  have hsymm : (e_W.trans e_W').symm w'' = e_W.symm (e_W'.symm w'') :=
    (e_W.trans e_W').symm_apply_eq.mpr (by simp)
  rw [hsymm]
  rfl

theorem mem_map_orthogonal_iff (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') {v' : V'} :
    v' ∈ (P.map e_W e_V).orthogonal ↔ e_V.symm v' ∈ P.orthogonal := by
  simp only [mem_orthogonal_iff, map_embed]
  refine ⟨fun h w ↦ ?_, fun h w' ↦ ?_⟩
  · have hw := h (e_W w)
    rw [e_W.symm_apply_apply] at hw
    rw [← e_V.polar_apply, e_V.apply_symm_apply]
    exact hw
  · conv_lhs => rw [← e_V.apply_symm_apply v']
    rw [e_V.polar_apply]
    exact h (e_W.symm w')

/-- **Intertwining of stabilizer embeddings.** Any pair of isometric equivalences `(e_W, e_V)`
intertwining the embeddings of two relevant pairs `P` and `P'` intertwines their stabilizer
embeddings `SO(Q_W) →* SO(Q_V)` and `SO(Q_W') →* SO(Q_V')`. -/
theorem stabilizerHom_specialOrthogonalGroupCongr [FiniteDimensional K W] [FiniteDimensional K W']
    {j' : ℕ} (P : OrthogonalRelevantPair Q_W Q_V j)
    (P' : OrthogonalRelevantPair Q_W' Q_V' j')
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V')
    (hcomm : e_V.toIsometry.comp P.embed = P'.embed.comp e_W.toIsometry)
    (g : specialOrthogonalGroup Q_W) :
    e_V.specialOrthogonalGroupCongr (P.stabilizerHom g) =
      P'.stabilizerHom (e_W.specialOrthogonalGroupCongr g) := by
  have himg (w : W) : e_V (P.embed w) = P'.embed (e_W w) :=
    DFunLike.congr_fun hcomm w
  have horth {v' : V'} (hv' : v' ∈ P'.orthogonal) : e_V.symm v' ∈ P.orthogonal := by
    rw [mem_orthogonal_iff]
    intro w
    rw [← e_V.polar_apply, e_V.apply_symm_apply, himg w]
    exact P'.mem_orthogonal_iff.mp hv' (e_W w)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v'
  -- Verify equality on the complementary decomposition `range P'.embed ⊕ P'.orthogonal`.
  obtain ⟨⟨w', u'⟩, rfl⟩ := P'.ambientIsometryEquiv.toLinearEquiv.surjective v'
  rw [QuadraticMap.IsometryEquiv.coe_toLinearEquiv, P'.ambientIsometryEquiv_apply]
  simp only [map_add, IsometryEquiv.coe_specialOrthogonalGroupCongr_apply]
  rw [P'.stabilizerHom_apply_embed, P'.stabilizerHom_apply_of_mem_orthogonal _ u'.property]
  congr 1
  · have hsymm : e_V.symm (P'.embed w') = P.embed (e_W.symm w') :=
      e_V.symm_apply_eq.mpr (by simpa using (himg (e_W.symm w')).symm)
    rw [hsymm, P.stabilizerHom_apply_embed, himg,
      IsometryEquiv.coe_specialOrthogonalGroupCongr_apply]
  · rw [P.stabilizerHom_apply_of_mem_orthogonal g (horth u'.property), e_V.apply_symm_apply]

/-- Transporting a relevant pair along `(e_W, e_V)` intertwines the stabilizer embeddings. -/
theorem stabilizerHom_map [FiniteDimensional K W] [FiniteDimensional K W']
    (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V')
    (g : specialOrthogonalGroup Q_W) :
    (P.map e_W e_V).stabilizerHom (e_W.specialOrthogonalGroupCongr g) =
      e_V.specialOrthogonalGroupCongr (P.stabilizerHom g) := by
  refine (stabilizerHom_specialOrthogonalGroupCongr P (P.map e_W e_V) e_W e_V ?_ g).symm
  ext w
  simp

end Map

end OrthogonalRelevantPair

namespace FramedOrthogonalRelevantPair

section Map

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V W' V' : Type*} [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]
  [AddCommGroup W'] [Module K W'] [AddCommGroup V'] [Module K V']
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V}
  {Q_W' : QuadraticForm K W'} {Q_V' : QuadraticForm K V'} {j : ℕ}

private theorem map_orthogonal_eq (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (LinearMap.BilinForm.orthogonal Q_V.polarBilin (LinearMap.range F.embed.toLinearMap)).map
        e_V.toLinearMap =
      LinearMap.BilinForm.orthogonal Q_V'.polarBilin
        (LinearMap.range
          (e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)).toLinearMap) := by
  have hrange :
      LinearMap.range (e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)).toLinearMap =
        (LinearMap.range F.embed.toLinearMap).map e_V.toLinearMap := by
    ext v'
    simp only [QuadraticMap.Isometry.toLinearMap_comp, LinearMap.mem_range,
      LinearMap.comp_apply, QuadraticMap.Isometry.coe_toLinearMap, LinearEquiv.coe_toLinearMap,
      Submodule.mem_map]
    refine ⟨fun ⟨w', hw'⟩ ↦ ⟨F.embed (e_W.symm w'), ⟨e_W.symm w', rfl⟩, hw'⟩, ?_⟩
    rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨e_W w, by simp⟩
  rw [hrange]
  exact e_V.map_orthogonal_polarBilin (LinearMap.range F.embed.toLinearMap)

private noncomputable def mapSubmoduleEquiv (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (Q_V.restrict
        (LinearMap.BilinForm.orthogonal Q_V.polarBilin
          (LinearMap.range F.embed.toLinearMap))).IsometryEquiv
      (Q_V'.restrict
        (LinearMap.BilinForm.orthogonal Q_V'.polarBilin
          (LinearMap.range
            (e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)).toLinearMap))) where
  toFun u := ⟨e_V u, by
    rw [← map_orthogonal_eq F e_W e_V]
    exact Submodule.mem_map_of_mem u.property⟩
  invFun u' := ⟨e_V.symm u', by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro _ ⟨w, rfl⟩
    have hu' := LinearMap.BilinForm.mem_orthogonal_iff.mp u'.property
      ((e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)) (e_W w)) ⟨e_W w, rfl⟩
    rw [QuadraticMap.polarBilin_apply_apply, ← e_V.polar_apply, e_V.apply_symm_apply]
    simpa [QuadraticMap.polarBilin_apply_apply] using hu'⟩
  left_inv _ := Subtype.ext (e_V.symm_apply_apply _)
  right_inv _ := Subtype.ext (e_V.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (e_V.map_add _ _)
  map_smul' _ _ := Subtype.ext (e_V.map_smul _ _)
  map_app' u := e_V.map_app (u : V)

/-- Transport a framed orthogonal relevant pair along isometric equivalences `(e_W, e_V)`. -/
noncomputable def map (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    FramedOrthogonalRelevantPair Q_W' Q_V' j where
  embed := e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)
  nondegenerate_domain := e_W.nondegenerate_iff.mp F.nondegenerate_domain
  lineCoeff := F.lineCoeff
  complementEquiv := (mapSubmoduleEquiv F e_W e_V).symm.trans F.complementEquiv

@[simp]
theorem map_toOrthogonalRelevantPair (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (F.map e_W e_V).toOrthogonalRelevantPair =
      F.toOrthogonalRelevantPair.map e_W e_V :=
  (rfl)

@[simp]
theorem map_embed (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') (w' : W') :
    (F.map e_W e_V).embed w' = e_V (F.embed (e_W.symm w')) :=
  (rfl)

@[simp]
theorem map_lineCoeff (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (F.map e_W e_V).lineCoeff = F.lineCoeff :=
  (rfl)

@[simp]
theorem map_complementEquiv_symm (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V')
    (y : (Fin j → Fin 2 → K) × K) :
    ((F.map e_W e_V).complementEquiv.symm y : V') = e_V (F.complementEquiv.symm y : V) := by
  set u : LinearMap.BilinForm.orthogonal Q_V.polarBilin (LinearMap.range F.embed.toLinearMap) :=
    F.complementEquiv.symm y
  have hu : e_V (u : V) ∈ LinearMap.BilinForm.orthogonal Q_V'.polarBilin
      (LinearMap.range (e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)).toLinearMap) := by
    rw [← map_orthogonal_eq F e_W e_V]
    exact Submodule.mem_map_of_mem u.property
  have hinv : (mapSubmoduleEquiv F e_W e_V).symm ⟨e_V (u : V), hu⟩ = u :=
    Subtype.ext (e_V.symm_apply_apply (u : V))
  have hsub_u : (F.map e_W e_V).complementEquiv ⟨e_V (u : V), hu⟩ = y :=
    (congrArg F.complementEquiv hinv).trans (F.complementEquiv.apply_symm_apply y)
  exact congrArg Subtype.val ((F.map e_W e_V).complementEquiv.symm_apply_eq.mpr hsub_u.symm)

@[simp]
theorem map_lineVector (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (F.map e_W e_V).lineVector = e_V F.lineVector :=
  F.map_complementEquiv_symm e_W e_V (0, 1)

@[simp]
theorem map_refl (F : FramedOrthogonalRelevantPair Q_W Q_V j) :
    F.map (IsometryEquiv.refl Q_W) (IsometryEquiv.refl Q_V) = F := by
  ext y
  · rfl
  · simp

theorem map_trans {W'' V'' : Type*} [AddCommGroup W''] [Module K W'']
    [AddCommGroup V''] [Module K V''] {Q_W'' : QuadraticForm K W''}
    {Q_V'' : QuadraticForm K V''} (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V')
    (e_W' : Q_W'.IsometryEquiv Q_W'') (e_V' : Q_V'.IsometryEquiv Q_V'') :
    (F.map e_W e_V).map e_W' e_V' = F.map (e_W.trans e_W') (e_V.trans e_V') := by
  ext y
  · simp only [map_embed]
    have hsymm : (e_W.trans e_W').symm y = e_W.symm (e_W'.symm y) :=
      (e_W.trans e_W').symm_apply_eq.mpr (by simp)
    rw [hsymm]
    rfl
  · simp

end Map

end FramedOrthogonalRelevantPair

/-! ### Scalar extension -/

section BaseChange

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup V] [Module K V]
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V} {j : ℕ}

namespace OrthogonalRelevantPair

/-- Scalar extension of `W^⊥` equals the orthogonal complement of `range (embed.baseChange L)`
in `L ⊗[K] V`. -/
theorem orthogonal_baseChange_eq (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    P.orthogonal.baseChange L =
      LinearMap.BilinForm.orthogonal (Q_V.baseChange L).polarBilin
        (LinearMap.range (P.embed.baseChange L).toLinearMap) := by
  set S := LinearMap.range P.embed.toLinearMap
  set S_L := LinearMap.range (P.embed.baseChange L).toLinearMap
  set U_L := LinearMap.BilinForm.orthogonal (Q_V.baseChange L).polarBilin S_L
  have hS_L : S.baseChange L = S_L := by
    rw [LinearMap.baseChange_range, ← Isometry.baseChange_toLinearMap]
  have hle : P.orthogonal.baseChange L ≤ U_L := by
    rw [Submodule.baseChange_le_iff_le_comap]
    intro v hv
    rw [Submodule.mem_comap]
    -- Expose `Submodule.toBaseChange` as the pure tensor `(1 : L) ⊗ₜ[K] v`.
    change (1 : L) ⊗ₜ[K] v ∈ U_L
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    have hx' : x ∈ S.baseChange L := hS_L.symm ▸ hx
    have hker :
        S.baseChange L ≤ LinearMap.ker ((Q_V.baseChange L).polarBilin.flip (1 ⊗ₜ v)) := by
      rw [Submodule.baseChange_le_iff_le_comap]
      rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_comap]
      -- Expose `Submodule.toBaseChange` as `(1 : L) ⊗ₜ[K] P.embed w`.
      change (1 : L) ⊗ₜ[K] (P.embed w) ∈
        LinearMap.ker ((Q_V.baseChange L).polarBilin.flip (1 ⊗ₜ v))
      simp only [LinearMap.mem_ker, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply,
        QuadraticForm.polar_baseChange_tmul]
      rw [P.mem_orthogonal_iff.mp hv w, zero_smul]
    exact hker hx'
  refine le_antisymm hle fun x hx ↦ ?_
  have hsup : S_L ⊔ P.orthogonal.baseChange L = ⊤ := by
    rw [← hS_L, ← Submodule.baseChange_sup, P.isCompl_orthogonal.sup_eq_top,
      Submodule.baseChange_top]
  have hndW : (Q_W.baseChange L).Nondegenerate :=
    QuadraticForm.Nondegenerate.baseChange P.nondegenerate_domain
  have hinj : Function.Injective (P.embed.baseChange L) :=
    (P.embed.baseChange L).injective_of_radical_eq_bot hndW.radical_eq_bot
  let eRange : (Q_W.baseChange L).IsometryEquiv ((Q_V.baseChange L).restrict S_L) :=
    { toLinearEquiv := LinearEquiv.ofInjective (P.embed.baseChange L).toLinearMap hinj
      map_app' w := (P.embed.baseChange L).map_app w }
  have : FiniteDimensional L S_L := Module.Finite.equiv eRange.toLinearEquiv
  have hcomp : IsCompl S_L U_L :=
    (eRange.nondegenerate_iff.mp hndW).isCompl_orthogonal
  obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := x))
  have hsU : s ∈ U_L := by
    have : s = (s + u) - u := (add_sub_cancel_right s u).symm
    rw [this]
    exact U_L.sub_mem hx (hle hu)
  have hs0 : s = 0 := Submodule.disjoint_def.mp hcomp.disjoint s hs hsU
  simpa [hs0] using hu

/-- The canonical isometric equivalence identifying `(Q_V|_{W^⊥}).baseChange L` with
`(Q_V.baseChange L)|_{(range (embed.baseChange L))^⊥}`. -/
noncomputable def orthogonalBaseChangeIsometryEquiv (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (QuadraticForm.baseChange L (Q_V.restrict P.orthogonal)).IsometryEquiv
      ((Q_V.baseChange L).restrict
        (LinearMap.BilinForm.orthogonal (Q_V.baseChange L).polarBilin
          (LinearMap.range (P.embed.baseChange L).toLinearMap))) where
  toLinearEquiv :=
    (Submodule.toBaseChange.toLinearEquiv L P.orthogonal).trans
      (LinearEquiv.ofEq _ _ (P.orthogonal_baseChange_eq L))
  map_app' x := by
    set φ := (Submodule.toBaseChange.toLinearEquiv L P.orthogonal).trans
      (LinearEquiv.ofEq _ _ (P.orthogonal_baseChange_eq L))
    have h : ((Q_V.baseChange L).restrict _).comp φ.toLinearMap =
        QuadraticForm.baseChange L (Q_V.restrict P.orthogonal) := by
      apply baseChange_ext
      intro u
      simp [φ]
    exact DFunLike.congr_fun h x

@[simp]
theorem coe_orthogonalBaseChangeIsometryEquiv_tmul (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)]
    (a : L) (u : P.orthogonal) :
    ((P.orthogonalBaseChangeIsometryEquiv L (a ⊗ₜ u) : _) : L ⊗[K] V) = a ⊗ₜ (u : V) :=
  (rfl)

/-- Extend scalars of an unframed orthogonal relevant pair to a field extension `L / K`. -/
noncomputable def baseChange (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    OrthogonalRelevantPair (Q_W.baseChange L) (Q_V.baseChange L) j where
  embed := P.embed.baseChange L
  nondegenerate_domain := QuadraticForm.Nondegenerate.baseChange P.nondegenerate_domain
  exists_complement := by
    obtain ⟨c, ⟨e⟩⟩ := P.exists_complement
    refine ⟨Units.map (algebraMap K L : K →* L) c, ⟨?_⟩⟩
    exact (P.orthogonalBaseChangeIsometryEquiv L).symm.trans
      ((e.baseChangeProd L).trans ((baseChangeHyperbolicSum (R := K) j L).prod
        (baseChangeLine (c : K) L)))

@[simp]
theorem baseChange_embed (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (P.baseChange L).embed = P.embed.baseChange L :=
  (rfl)

theorem baseChange_embed_tmul (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] (a : L) (w : W) :
    (P.baseChange L).embed (a ⊗ₜ w) = a ⊗ₜ P.embed w :=
  QuadraticMap.Isometry.baseChange_tmul P.embed a w

/-- Scalar extension commutes with the stabilizer embedding `SO(Q_W) →* SO(Q_V)`. -/
theorem stabilizerHom_baseChange [FiniteDimensional K V]
    (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)]
    (g : specialOrthogonalGroup Q_W) :
    specialOrthogonalGroupBaseChange (A := L) Q_V (P.stabilizerHom g) =
      (P.baseChange L).stabilizerHom (specialOrthogonalGroupBaseChange (A := L) Q_W g) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  obtain ⟨⟨w, u⟩, rfl⟩ := P.ambientIsometryEquiv.toLinearEquiv.surjective v
  rw [← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul',
    QuadraticMap.IsometryEquiv.coe_toLinearEquiv, P.ambientIsometryEquiv_apply,
    TensorProduct.tmul_add]
  simp only [LinearEquiv.coe_coe, map_smul, map_add,
    specialOrthogonalGroupBaseChange_apply_tmul]
  rw [P.stabilizerHom_apply_embed, P.stabilizerHom_apply_of_mem_orthogonal g u.property]
  congr 2
  · rw [← P.baseChange_embed_tmul L 1 w,
      (P.baseChange L).stabilizerHom_apply_embed,
      specialOrthogonalGroupBaseChange_apply_tmul, baseChange_embed_tmul]
  · have hu : (1 : L) ⊗ₜ[K] (u : V) ∈ (P.baseChange L).orthogonal := by
      rw [orthogonal, baseChange_embed, ← P.orthogonal_baseChange_eq L]
      exact Submodule.tmul_mem_baseChange_of_mem 1 u.property
    exact ((P.baseChange L).stabilizerHom_apply_of_mem_orthogonal _ hu).symm

end OrthogonalRelevantPair

namespace FramedOrthogonalRelevantPair

/-- Extend scalars of a framed orthogonal relevant pair to a field extension `L / K`. -/
noncomputable def baseChange (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    FramedOrthogonalRelevantPair (Q_W.baseChange L) (Q_V.baseChange L) j where
  embed := F.embed.baseChange L
  nondegenerate_domain := QuadraticForm.Nondegenerate.baseChange F.nondegenerate_domain
  lineCoeff := Units.map (algebraMap K L : K →* L) F.lineCoeff
  complementEquiv :=
    (F.toOrthogonalRelevantPair.orthogonalBaseChangeIsometryEquiv L).symm.trans
      ((F.complementEquiv.baseChangeProd L).trans ((baseChangeHyperbolicSum (R := K) j L).prod
        (baseChangeLine (F.lineCoeff : K) L)))

@[simp]
theorem baseChange_toOrthogonalRelevantPair (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (F.baseChange L).toOrthogonalRelevantPair =
      F.toOrthogonalRelevantPair.baseChange L :=
  (rfl)

@[simp]
theorem baseChange_embed (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (F.baseChange L).embed = F.embed.baseChange L :=
  (rfl)

@[simp]
theorem baseChange_lineCoeff (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (F.baseChange L).lineCoeff = Units.map (algebraMap K L : K →* L) F.lineCoeff :=
  (rfl)

@[simp]
theorem baseChange_lineVector (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (F.baseChange L).lineVector = (1 : L) ⊗ₜ[K] F.lineVector := by
  have hmem : (1 : L) ⊗ₜ[K] F.lineVector ∈ (F.baseChange L).orthogonal := by
    rw [orthogonal, baseChange_toOrthogonalRelevantPair, OrthogonalRelevantPair.orthogonal,
      OrthogonalRelevantPair.baseChange_embed,
      ← F.toOrthogonalRelevantPair.orthogonal_baseChange_eq L]
    exact Submodule.tmul_mem_baseChange_of_mem 1 F.lineVector_mem_orthogonal
  have h :
      (F.baseChange L).complementEquiv ⟨(1 : L) ⊗ₜ[K] F.lineVector, hmem⟩ =
        (0, (1 : L)) := by
    let u0 : LinearMap.BilinForm.orthogonal Q_V.polarBilin (LinearMap.range F.embed.toLinearMap) :=
      ⟨F.lineVector, F.lineVector_mem_orthogonal⟩
    have hline : F.complementEquiv u0 = (0, (1 : K)) := by
      simp [u0, lineVector]
    have hinv :
        (F.toOrthogonalRelevantPair.orthogonalBaseChangeIsometryEquiv L).symm
            ⟨(1 : L) ⊗ₜ[K] F.lineVector, hmem⟩ =
          (1 : L) ⊗ₜ[K] u0 :=
      (F.toOrthogonalRelevantPair.orthogonalBaseChangeIsometryEquiv L).symm_apply_eq.mpr
        (Subtype.ext rfl)
    have hcomp :
        (F.baseChange L).complementEquiv ⟨(1 : L) ⊗ₜ[K] F.lineVector, hmem⟩ =
          ((baseChangeHyperbolicSum (R := K) j L).prod (baseChangeLine (F.lineCoeff : K) L))
            ((F.complementEquiv.baseChangeProd L)
              ((F.toOrthogonalRelevantPair.orthogonalBaseChangeIsometryEquiv L).symm
                ⟨(1 : L) ⊗ₜ[K] F.lineVector, hmem⟩)) :=
      rfl
    rw [hcomp, hinv, IsometryEquiv.baseChangeProd_tmul, hline, IsometryEquiv.prod_apply]
    refine Prod.ext ?_ (by simp)
    ext i k
    simp
  have hsymm := congrArg (fun x : (F.baseChange L).orthogonal ↦ (x : L ⊗[K] V))
    ((F.baseChange L).complementEquiv.symm_apply_eq.mpr h.symm)
  exact hsymm

end FramedOrthogonalRelevantPair

end BaseChange

/-! ### Canonical product model and witnesses -/

namespace FramedOrthogonalRelevantPair

section OfProd

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W : Type*} [AddCommGroup W] [Module K W]
  (Q_W : QuadraticForm K W) (hW : Q_W.Nondegenerate) (j : ℕ) (c : Kˣ)

/-- The canonical framed orthogonal relevant pair embedding `(W, Q_W)` as the first summand of
`Q_W ⊥ (H^j ⊥ ⟨c⟩)`. -/
noncomputable def ofProd :
    FramedOrthogonalRelevantPair Q_W
      (Q_W.prod ((hyperbolicSum K j).prod ((c : K) • QuadraticMap.sq))) j where
  embed := QuadraticMap.Isometry.inl Q_W ((hyperbolicSum K j).prod ((c : K) • QuadraticMap.sq))
  nondegenerate_domain := hW
  lineCoeff := c
  complementEquiv :=
    { toFun x := x.val.2
      invFun y := ⟨(0, y), by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        rintro _ ⟨w, rfl⟩
        simp [QuadraticMap.polar]⟩
      left_inv x := by
        have hx1 : (x : W × (Fin j → Fin 2 → K) × K).1 = 0 := by
          have hpol := LinearMap.BilinForm.mem_orthogonal_iff.mp x.property
          refine (nondegenerate_polar_iff.mpr hW).1 _ fun w ↦ ?_
          have hw := hpol (w, 0) ⟨w, rfl⟩
          rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] at hw
          simpa [QuadraticMap.polar] using hw
        exact Subtype.ext (Prod.ext hx1.symm rfl)
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      map_app' x := by
        have hx1 : (x : W × (Fin j → Fin 2 → K) × K).1 = 0 := by
          have hpol := LinearMap.BilinForm.mem_orthogonal_iff.mp x.property
          refine (nondegenerate_polar_iff.mpr hW).1 _ fun w ↦ ?_
          have hw := hpol (w, 0) ⟨w, rfl⟩
          rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] at hw
          simpa [QuadraticMap.polar] using hw
        simp [hx1] }

@[simp]
theorem ofProd_embed (w : W) : (ofProd Q_W hW j c).embed w = (w, (0, 0)) :=
  (rfl)

@[simp]
theorem ofProd_lineCoeff : (ofProd Q_W hW j c).lineCoeff = c :=
  (rfl)

@[simp]
theorem ofProd_lineVector : (ofProd Q_W hW j c).lineVector = (0, (0, 1)) :=
  (rfl)

@[simp]
theorem ofProd_stabilizerHom [FiniteDimensional K W] (g : specialOrthogonalGroup Q_W) :
    (ofProd Q_W hW j c).stabilizerHom g =
      specialOrthogonalGroupProd Q_W ((hyperbolicSum K j).prod ((c : K) • QuadraticMap.sq))
        (g, 1) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rcases x with ⟨w, y⟩
  have hy : (0, y) ∈ (ofProd Q_W hW j c).orthogonal := by
    rw [OrthogonalRelevantPair.mem_orthogonal_iff]
    intro w'
    simp [QuadraticMap.polar]
  have hsplit : (w, y) = (ofProd Q_W hW j c).embed w + (0, y) := by simp
  rw [hsplit, map_add, map_add]
  dsimp only [FramedOrthogonalRelevantPair.stabilizerHom]
  rw [← (ofProd Q_W hW j c).toOrthogonalRelevantPair_embed,
    (ofProd Q_W hW j c).toOrthogonalRelevantPair.stabilizerHom_apply_embed,
    (ofProd Q_W hW j c).toOrthogonalRelevantPair.stabilizerHom_apply_of_mem_orthogonal g hy]
  simp

end OfProd

/-! ### Non-vacuous dimension witnesses -/

/-- For a zero-dimensional smaller space `W = Fin 0 → K` and `j = 0`, the canonical relevant pair
has trivial stabilizer group `SO(Q_W)` and ambient dimension `1`. -/
theorem finrank_ofProd_zero_zero (K : Type*) [Field K] [Invertible (2 : K)] (c : Kˣ) :
    Module.finrank K ((Fin 0 → K) × ((Fin 0 → Fin 2 → K) × K)) = 1 ∧
      Subsingleton (specialOrthogonalGroup (0 : QuadraticForm K (Fin 0 → K))) ∧
      (Module.finrank K ((Fin 0 → K) × ((Fin 0 → Fin 2 → K) × K)) -
        Module.finrank K (Fin 0 → K)) % 2 = 1 := by
  refine ⟨by simp [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self], ?_, ?_⟩
  · refine ⟨fun g₁ g₂ ↦ Subtype.ext (LinearEquiv.ext fun x ↦ Subsingleton.elim _ _)⟩
  · exact (ofProd (0 : QuadraticForm K (Fin 0 → K))
      (by rw [nondegenerate_iff_radical_eq_bot]; exact Submodule.eq_bot_of_subsingleton)
      0 c).toOrthogonalRelevantPair.odd_codimension

/-- A positive-dimension witness with `dim W = 2`, `j = 1`, and ambient dimension `d = 5`. -/
theorem finrank_ofProd_hyperbolicPlane_one (K : Type*) [Field K] [Invertible (2 : K)] (c : Kˣ) :
    let F := ofProd (hyperbolicPlane K) nondegenerate_hyperbolicPlane 1 c
    Module.finrank K ((Fin 2 → K) × ((Fin 1 → Fin 2 → K) × K)) = 5 ∧
      ((hyperbolicPlane K).prod ((hyperbolicSum K 1).prod ((c : K) • QuadraticMap.sq)))
        F.lineVector ≠ 0 ∧
      (Module.finrank K ((Fin 2 → K) × ((Fin 1 → Fin 2 → K) × K)) -
        Module.finrank K (Fin 2 → K)) % 2 = 1 := by
  let F := ofProd (hyperbolicPlane K) nondegenerate_hyperbolicPlane 1 c
  refine ⟨by simp [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self],
    F.apply_lineVector_ne_zero, F.toOrthogonalRelevantPair.odd_codimension⟩

end FramedOrthogonalRelevantPair

end TauCeti
