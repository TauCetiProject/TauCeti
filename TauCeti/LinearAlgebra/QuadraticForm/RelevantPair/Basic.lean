/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.Prod
import TauCeti.LinearAlgebra.QuadraticForm.Basic

/-!
# Orthogonal relevant pairs and framed complements

Given quadratic spaces `(W, Q_W)` and `(V, Q_V)` over a field `K` of characteristic not two, a
*relevant pair* of hyperbolic index `j` consists of an isometric embedding `W →qᵢ Q_V` with
nondegenerate domain whose orthogonal complement `W^⊥` is isometric to `H^j ⊥ ⟨c⟩` for some
nonzero scalar `c ∈ Kˣ`, where `H^j` is the orthogonal sum of `j` hyperbolic planes. A *framed*
orthogonal relevant pair equips this datum with a chosen scalar `c` and an explicit isometric
equivalence `W^⊥ ≃qᵢ H^j ⊥ ⟨c⟩`, distinguishing an anisotropic line generator.

Because `W` is nondegenerate and finite-dimensional, `V` decomposes orthogonally as `W ⊥ W^⊥`,
so `V` is itself finite-dimensional and nondegenerate of dimension `dim W + 2j + 1`.

## Main definitions

* `TauCeti.hyperbolicSum R j`: the orthogonal sum of `j` copies of the hyperbolic plane
  `⟨1, -1⟩`.
* `TauCeti.OrthogonalRelevantPair Q_W Q_V j`: an isometric embedding `W →qᵢ Q_V` with
  nondegenerate domain whose orthogonal complement is isometric to `H^j ⊥ ⟨c⟩`.
* `TauCeti.FramedOrthogonalRelevantPair Q_W Q_V j`: an orthogonal relevant pair equipped with a
  chosen unit `lineCoeff : Kˣ` and an explicit framing `W^⊥ ≃qᵢ H^j ⊥ ⟨lineCoeff⟩`.
* `TauCeti.OrthogonalRelevantPair.ambientIsometryEquiv`: the orthogonal splitting
  `Q_W ⊥ Q_V|_{W^⊥} ≃qᵢ Q_V`.

## Main results

* `TauCeti.nondegenerate_hyperbolicSum`: `hyperbolicSum R j` is nondegenerate.
* `TauCeti.OrthogonalRelevantPair.finrank_eq`, `TauCeti.OrthogonalRelevantPair.odd_codimension`:
  the ambient dimension satisfies `dim V = dim W + 2j + 1`, so `dim V - dim W` is odd.

## References

* D. Jiang and L. Zhang, *Arthur parameters and cuspidal automorphic modules of classical groups*,
  Ann. of Math. 191 (2020), §2.1 and §2.4.
* W. T. Gan, B. H. Gross, and D. Prasad, *Symplectic local root numbers, central critical
  `L` values, and restriction problems in the representation theory of classical groups*,
  Astérisque 346 (2012), §2 and §12.
-/

public section

open Module QuadraticMap QuadraticForm TauCeti.QuadraticMap

namespace TauCeti

/-! ### Split hyperbolic sums -/

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
@[expose] def toOrthogonalRelevantPair (F : FramedOrthogonalRelevantPair Q_W Q_V j) :
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

/-- Unfolding lemma for `lineVector`. -/
theorem lineVector_eq : F.lineVector = (F.complementEquiv.symm (0, 1) : V) := by
  rfl

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

end TauCeti
