/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Defs
public import TauCeti.Algebra.Homology.DG.Twisted.Complex
public import TauCeti.CategoryTheory.DG.ShiftClosure.SingleObj
public import TauCeti.CategoryTheory.DG.Twisted.OneSided

/-!
# Twisting cocycles give one-sided twisted complexes

Let `(A, d)` be a differential graded algebra and `⋆` the unique object of its one-object
differential graded category `TauCeti.DGSingleObj h`.  In Mathlib's enriched factor order its
composition is the graded opposite product, `dgComp a b = (-1)^(|a| |b|) • (b * a)`
(`TauCeti.DGSingleObj.dgHomEquiv_dgComp`).  This file shows that a twisting cocycle `m` on a finite
set `P` of generators graded by `ind`, the data of the twisted complex `K_m` of
`TauCeti.Algebra.Homology.DG.Twisted.Complex`, gives a one-sided twisted complex of Bondal and
Kapranov over this category, that twisting cocycles correspond exactly to the Maurer–Cartan twists
of `⊕_x ⋆[-ind x]` that are strictly triangular for `ind`, and compares the two complexes.

The twisted complex is `T_m = (⊕_{x ∈ P} ⋆[-ind x], δ)`, an object of the additive closure of the
shift closure of the one-object category (`TauCeti.TwistingCocycle.shiftedGenerators`), with the
twisting matrix `δ = -mᵀ` whose entry from `x` to `y` is `-m y x`
(`TauCeti.TwistingCocycle.twistMatrix`).  Both the transpose and the shifts `-ind x` are forced.  A
morphism `⋆[r] ⟶ ⋆[s]` of degree one is an element of `A` of degree `1 + s - r`, which for
`r = -ind x` and `s = -ind y` is the degree `ind x - ind y + 1` of `m y x`.  Composing the entries
`δ x y` and `δ y z` multiplies `m z y * m y x`, in the order in which the twisting equation for
`m z x` multiplies them; the untransposed matrix would multiply in the opposite order, which over
a noncommutative algebra is a different equation (compare the right-free reading in
`TauCeti.Algebra.Homology.DG.Twisted.Noncommutative`).

* **The Maurer–Cartan equation is the twisting equation.**  The Maurer–Cartan equation
  `d δ = dgComp δ δ` of twisted objects, that is `d δ + δ ∘ δ = 0` in Keller's order, holds exactly
  when `m` satisfies `d (m x y) = Σ_z (-1)^(ind x - ind z) • (m x z * m z y)`
  (`TauCeti.TwistingCocycle.dgDifferential_twistMatrix_eq_dgComp_iff`).  In the entry from `x` to
  `z`, the sign `(-1)^(ind x - ind z)` of the differential of the shift closure and the signs of
  composition in the shift closure and in the one-object category combine to the twisting-equation
  sign `(-1)^(ind z - ind y)` times the common factor `-(-1)^(ind x - ind z)`.
* **One-sidedness and strict triangularity.**  Since `m y x` vanishes unless `ind x < ind y`, the
  twisted object `TauCeti.TwistingCocycle.toDGTwistedObject` is one-sided for the levels
  `N - ind x` (`TauCeti.TwistingCocycle.isOneSided_toDGTwistedObject`), so it lies in the
  pretriangulated envelope of the one-object category.  Conversely every degree-one Maurer–Cartan
  endomorphism of `⊕_x ⋆[-ind x]` that is strictly triangular for `ind`, that is whose entry from
  `x` to `y` vanishes when `ind y ≤ ind x`, comes from exactly one twisting cocycle
  (`TauCeti.TwistingCocycle.twistMatrixEquiv`).
* **The twisted complex `K_m` is a Hom complex.**  The Hom complex from `T_m` to `⋆[0]` is
  isomorphic, as a cochain complex, to the twisted complex `K_m` of the free rank-one module `A`, in
  which `x` sits in degree `-ind x` and `d x = Σ_y m x y · y`
  (`TauCeti.TwistingCocycle.dgHomComplexIso`).  In degree `n` the component of a morphism at `x` is
  multiplied by `(-1)^((n + 1) * ind x)`.

The one-object category of `A` needs the ground ring and the algebra in one universe, and the
summands of an object of the additive closure are indexed by a type in `Type`, so `R` and `A`
share a universe and the generators form a type `P : Type`.

## Main definitions

* `TauCeti.TwistingCocycle.shiftedGenerators`: the object `⊕_{x ∈ P} ⋆[-ind x]`.
* `TauCeti.TwistingCocycle.twistMatrix`: the degree-one endomorphism `-mᵀ` of it.
* `TauCeti.TwistingCocycle.toDGTwistedObject`: the twisted object `T_m` of a twisting cocycle.
* `TauCeti.TwistingCocycle.twistMatrixEquiv`: twisting cocycles are the Maurer–Cartan
  endomorphisms of `⊕_x ⋆[-ind x]` that are strictly triangular for `ind`.
* `TauCeti.TwistingCocycle.starTwistedObject`: the object `⋆[0]` of twisted objects.
* `TauCeti.TwistingCocycle.dgHomComplexIso`: the Hom complex from `T_m` to `⋆[0]` is `K_m`.

## Main results

* `TauCeti.TwistingCocycle.dgDifferential_twistMatrix_eq_dgComp_iff`: the Maurer–Cartan equation
  for `-mᵀ` is the twisting equation for `m`.
* `TauCeti.TwistingCocycle.isOneSided_toDGTwistedObject`: the twisted object of a twisting cocycle
  is one-sided.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 1.9 and Section 1.4.
* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.6, for the twisting
  equation `d δ + δ ∘ δ = 0` of twisted objects.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {R : Type u} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

namespace TwistingCocycle

open DGSingleObj

variable (h : IsDGAlgebra 𝒜 d) {P : Type} [Fintype P] (ind : P → ℤ)

/-- The object `⊕_{x ∈ P} ⋆[-ind x]` of the additive closure of the shift closure of the
one-object differential graded category of `A`: one copy of the unique object `⋆`, shifted by
`-ind x`, for each generator `x`. -/
-- This is reducible so that its summands are reducibly the shifted objects `⋆[-ind x]`.
abbrev shiftedGenerators : DGAdditiveClosure (DGShiftClosure (DGSingleObj h)) where
  ι := P
  X x := ⟨DGSingleObj.star h, -ind x⟩

variable {h ind}

/-- The degree-one morphism `⊕_x ⋆[-ind x] ⟶ ⊕_y ⋆[-ind y]` whose entry from `x` to `y` is
`-m y x`, the negative of the transpose of `m`. It has degree one exactly because `m y x` has
degree `ind x - ind y + 1`. -/
noncomputable def twistMatrix (m : P → P → A) (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1)) :
    DGHom R 1 (shiftedGenerators h ind) (shiftedGenerators h ind) :=
  (DGAdditiveClosure.dgHomEquiv R _ _ 1).symm fun x y ↦
    ofShiftCoeff (-m y x) <| by
      rw [show 1 + (-ind y - -ind x) = ind x - ind y + 1 by ring]
      exact neg_mem (hm y x)

/-- The entry from `x` to `y` of `TauCeti.TwistingCocycle.twistMatrix m` is `-m y x`. -/
@[simp]
theorem shiftCoeff_twistMatrix (m : P → P → A) (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1))
    (x y : P) :
    shiftCoeff (DGAdditiveClosure.dgHomEquiv R _ _ 1 (twistMatrix (h := h) m hm) x y) =
      -m y x := by
  simp [twistMatrix]

/-- The entries of the differential of `TauCeti.TwistingCocycle.twistMatrix m`, up to the common
sign `-(-1)^(ind x - ind z)`, are the differentials `d (m z x)`. -/
private theorem shiftCoeff_dgDifferential_twistMatrix (m : P → P → A)
    (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1)) (x z : P) :
    shiftCoeff (DGAdditiveClosure.dgHomEquiv R _ _ (1 + 1)
        (dgDifferential R 1 (twistMatrix (h := h) m hm)) x z) =
      (1 + (ind x - ind z)).negOnePow • d (m z x) := by
  rw [DGAdditiveClosure.dgHomEquiv_dgDifferential, shiftCoeff_dgDifferential,
    shiftCoeff_twistMatrix, map_neg, smul_neg, ← Units.neg_smul]
  congr 1
  rw [Int.negOnePow_add, Int.negOnePow_one, neg_one_mul]
  congr 2
  ring

/-- The entries of the square of `TauCeti.TwistingCocycle.twistMatrix m`, up to the common sign
`-(-1)^(ind x - ind z)`, are the right-hand sides of the twisting equation for `m z x`. -/
private theorem shiftCoeff_dgComp_twistMatrix (m : P → P → A)
    (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1)) (x z : P) :
    shiftCoeff (DGAdditiveClosure.dgHomEquiv R _ _ (1 + 1)
        (dgComp R (twistMatrix (h := h) m hm) (twistMatrix m hm) rfl) x z) =
      (1 + (ind x - ind z)).negOnePow • ∑ y, (ind z - ind y).negOnePow • (m z y * m y x) := by
  rw [DGAdditiveClosure.dgHomEquiv_dgComp, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [shiftCoeff_dgComp, shiftCoeff_twistMatrix, shiftCoeff_twistMatrix, neg_mul_neg, smul_smul,
    smul_smul]
  congr 1
  rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨(1 + ind x - ind y) * (ind y - ind z), by dsimp only; ring⟩

/-- **The Maurer–Cartan equation is the twisting equation.** The degree-one endomorphism of
`⊕_x ⋆[-ind x]` with entries `-m y x` satisfies the Maurer–Cartan equation `d δ = dgComp δ δ` of
twisted objects exactly when `m` satisfies the twisting equation
`d (m x y) = Σ_z (-1) ^ (ind x - ind z) • (m x z * m z y)`. -/
theorem dgDifferential_twistMatrix_eq_dgComp_iff (m : P → P → A)
    (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1)) :
    dgDifferential R 1 (twistMatrix (h := h) m hm) = dgComp R (twistMatrix m hm) (twistMatrix m hm)
        rfl ↔
      ∀ x y, d (m x y) = ∑ z, (ind x - ind z).negOnePow • (m x z * m z y) := by
  constructor
  · intro hmc z x
    have hxz := congrArg (fun δ ↦ shiftCoeff (DGAdditiveClosure.dgHomEquiv R _ _ (1 + 1) δ x z))
      hmc
    dsimp only at hxz
    rw [shiftCoeff_dgDifferential_twistMatrix, shiftCoeff_dgComp_twistMatrix] at hxz
    exact smul_left_cancel _ hxz
  · intro htw
    refine DGAdditiveClosure.dgHom_ext R fun x z ↦ shiftCoeff_injective ?_
    rw [shiftCoeff_dgDifferential_twistMatrix, shiftCoeff_dgComp_twistMatrix, htw]

/-- The underlying element `-m y x` of the entry from `x` to `y` of a degree-one endomorphism of
`⊕_x ⋆[-ind x]` has the degree `ind x - ind y + 1` of an entry of a twisting cocycle. -/
theorem neg_shiftCoeff_mem (δ : DGHom R 1 (shiftedGenerators h ind) (shiftedGenerators h ind))
    (x y : P) :
    -shiftCoeff (DGAdditiveClosure.dgHomEquiv R _ _ 1 δ y x) ∈ 𝒜 (ind y - ind x + 1) := by
  have hmem := shiftCoeff_mem (DGAdditiveClosure.dgHomEquiv R _ _ 1 δ y x)
  dsimp only at hmem
  rw [show 1 + (-ind x - -ind y) = ind y - ind x + 1 by ring] at hmem
  exact neg_mem hmem

/-- Every degree-one endomorphism of `⊕_x ⋆[-ind x]` is the twist of the matrix read off from its
entries: `m x y` is minus the element underlying the entry from `y` to `x`. -/
theorem twistMatrix_neg_shiftCoeff
    (δ : DGHom R 1 (shiftedGenerators h ind) (shiftedGenerators h ind)) :
    twistMatrix (fun x y ↦ -shiftCoeff (DGAdditiveClosure.dgHomEquiv R _ _ 1 δ y x))
        (neg_shiftCoeff_mem δ) = δ :=
  DGAdditiveClosure.dgHom_ext R fun x y ↦ shiftCoeff_injective <| by
    rw [shiftCoeff_twistMatrix, neg_neg]

/-- The entry from `x` to `y` of the twisting matrix of a twisting cocycle vanishes when
`ind y ≤ ind x`. -/
theorem dgHomEquiv_twistMatrix_eq_zero (m : TwistingCocycle 𝒜 d P ind) {x y : P}
    (hyx : ind y ≤ ind x) :
    DGAdditiveClosure.dgHomEquiv R _ _ 1 (twistMatrix (h := h) m.m m.mem_graded) x y = 0 :=
  shiftCoeff_injective <| by rw [shiftCoeff_twistMatrix, m.one_sided y x hyx, neg_zero, map_zero]

variable (h) in
/-- **A twisting cocycle is a one-sided twisted complex.** The twisting cocycle `m` on `P` makes
`⊕_{x ∈ P} ⋆[-ind x]` a twisted object of the additive closure of the shift closure of the
one-object differential graded category of `A`, with twisting matrix `-mᵀ`: the entry from `x` to
`y` is `-m y x`. -/
-- This is reducible so that the underlying object and the twist are reducibly
-- `shiftedGenerators h ind` and `twistMatrix m.m m.mem_graded`.
noncomputable abbrev toDGTwistedObject (m : TwistingCocycle 𝒜 d P ind) :
    DGTwistedObject R (DGAdditiveClosure (DGShiftClosure (DGSingleObj h))) where
  obj := shiftedGenerators h ind
  twist := twistMatrix m.m m.mem_graded
  dgDifferential_twist := (dgDifferential_twistMatrix_eq_dgComp_iff _ _).2 m.twisting

/-- **The twisted object of a twisting cocycle is one-sided**: the entry from `x` to `y` of its
twisting matrix is `-m y x`, which vanishes unless `ind x < ind y`, so the levels
`N - ind x`, for an upper bound `N` of the indices, strictly decrease along every nonzero entry. -/
theorem isOneSided_toDGTwistedObject (m : TwistingCocycle 𝒜 d P ind) :
    (m.toDGTwistedObject h).IsOneSided := by
  classical
  let N : ℤ := ((Finset.univ.sup fun x ↦ (ind x).toNat : ℕ) : ℤ)
  have hN (x : P) : ind x ≤ N :=
    (Int.self_le_toNat (ind x)).trans
      (Nat.cast_le.2 (Finset.le_sup (f := fun x ↦ (ind x).toNat) (Finset.mem_univ x)))
  refine (DGTwistedObject.isOneSided_iff _).2
    ⟨fun x ↦ (N - ind x).toNat, fun x y hxy ↦ dgHomEquiv_twistMatrix_eq_zero m ?_⟩
  dsimp only at hxy
  have := hN x
  have := hN y
  omega

variable (h ind) in
/-- **Twisting cocycles are the Maurer–Cartan twists of `⊕_x ⋆[-ind x]` that are strictly
triangular for `ind`.** A twisting
cocycle `m` on `P` corresponds to its twisting matrix `-mᵀ`, a degree-one endomorphism of
`⊕_x ⋆[-ind x]` which satisfies the Maurer–Cartan equation and whose entry from `x` to `y`
vanishes whenever `ind y ≤ ind x`; every such endomorphism arises from exactly one twisting
cocycle. -/
noncomputable def twistMatrixEquiv : TwistingCocycle 𝒜 d P ind ≃
    {δ : DGHom R 1 (shiftedGenerators h ind) (shiftedGenerators h ind) //
      dgDifferential R 1 δ = dgComp R δ δ rfl ∧
        ∀ x y, ind y ≤ ind x → DGAdditiveClosure.dgHomEquiv R _ _ 1 δ x y = 0} where
  toFun m := ⟨twistMatrix m.m m.mem_graded,
    (dgDifferential_twistMatrix_eq_dgComp_iff _ _).2 m.twisting,
    fun _ _ ↦ dgHomEquiv_twistMatrix_eq_zero m⟩
  invFun δ :=
    { m := fun x y ↦ -shiftCoeff (DGAdditiveClosure.dgHomEquiv R _ _ 1 δ.val y x)
      mem_graded := neg_shiftCoeff_mem δ.val
      twisting := (dgDifferential_twistMatrix_eq_dgComp_iff _ (neg_shiftCoeff_mem δ.val)).1 <| by
        rw [twistMatrix_neg_shiftCoeff]
        exact δ.property.1
      one_sided := fun x y hxy ↦ by rw [δ.property.2 y x hxy, map_zero, neg_zero] }
  left_inv m := TwistingCocycle.ext fun x y ↦ by
    dsimp only
    rw [shiftCoeff_twistMatrix, neg_neg]
  right_inv δ := Subtype.ext (twistMatrix_neg_shiftCoeff δ.val)

@[simp]
theorem coe_twistMatrixEquiv_apply (m : TwistingCocycle 𝒜 d P ind) :
    (twistMatrixEquiv h ind m : DGHom R 1 (shiftedGenerators h ind) (shiftedGenerators h ind)) =
      twistMatrix m.m m.mem_graded := by
  unfold twistMatrixEquiv
  rfl

@[simp]
theorem twistMatrixEquiv_symm_apply_m
    (δ : {δ : DGHom R 1 (shiftedGenerators h ind) (shiftedGenerators h ind) //
      dgDifferential R 1 δ = dgComp R δ δ rfl ∧
        ∀ x y, ind y ≤ ind x → DGAdditiveClosure.dgHomEquiv R _ _ 1 δ x y = 0}) (x y : P) :
    ((twistMatrixEquiv h ind).symm δ).m x y =
      -shiftCoeff (DGAdditiveClosure.dgHomEquiv R _ _ 1 δ.val y x) := by
  unfold twistMatrixEquiv
  rfl

/-! ### The twisted complex `K_m` as a Hom complex -/

variable (h) in
/-- The unique object `⋆` of the one-object differential graded category as the twisted object
`⋆[0]`: the one-term sum of its unshifted copy, with zero twist. -/
-- This is reducible so that its only summand is reducibly `⋆[0]`.
noncomputable abbrev starTwistedObject :
    DGTwistedObject R (DGAdditiveClosure (DGShiftClosure (DGSingleObj h))) :=
  DGTwistedObject.ofObj R ⟨PUnit, fun _ ↦ ⟨DGSingleObj.star h, 0⟩⟩

variable (h) in
/-- The twisted object `⋆[0]` is the image of `⋆` under the embeddings of the one-object
differential graded category into its shift closure, its additive closure and its twisted
objects. -/
theorem starTwistedObject_eq_embedding_obj : starTwistedObject h = (DGTwistedObject.embedding R).obj
    ((DGAdditiveClosure.embedding R).obj ((DGShiftClosure.ι R).obj (DGSingleObj.star h))) := by
  rw [DGTwistedObject.embedding_obj, DGAdditiveClosure.embedding_obj, DGShiftClosure.ι_obj]

variable (m : TwistingCocycle 𝒜 d P ind)

/-- The degree-`n` morphisms `T_m ⟶ ⋆[0]` are the total-degree-`n` elements of `P → A`: the value
at `x` is `(-1)^((n + 1) * ind x)` times the element of degree `n + ind x` underlying the component
`⋆[-ind x] ⟶ ⋆[0]`. -/
private noncomputable def homEquiv (n : ℤ) :
    DGHom R n (m.toDGTwistedObject h) (starTwistedObject h) ≃ₗ[R] twistedTotalGrading 𝒜 ind n where
  toFun f := ⟨fun x ↦ ((n + 1) * ind x).negOnePow • shiftCoeff
      (DGAdditiveClosure.dgHomEquiv R _ _ n (DGTwistedObject.dgHomEquiv R _ _ n f) x PUnit.unit),
    mem_twistedTotalGrading_iff.2 fun x ↦ by
      have hmem := shiftCoeff_mem
        (DGAdditiveClosure.dgHomEquiv R _ _ n (DGTwistedObject.dgHomEquiv R _ _ n f) x PUnit.unit)
      dsimp only at hmem
      rw [show n + (0 - -ind x) = n + ind x by ring] at hmem
      exact Submodule.smul_of_tower_mem _ _ hmem⟩
  invFun g := (DGTwistedObject.dgHomEquiv R _ _ n).symm <|
    (DGAdditiveClosure.dgHomEquiv R _ _ n).symm fun x _ ↦
      ofShiftCoeff (((n + 1) * ind x).negOnePow • (g : P → A) x) <| by
        rw [show n + ((0 : ℤ) - -ind x) = n + ind x by ring]
        exact Submodule.smul_of_tower_mem _ _ (mem_twistedTotalGrading_iff.1 g.property x)
  map_add' f g := Subtype.ext <| funext fun x ↦ by simp [smul_add]
  map_smul' r f := Subtype.ext <| funext fun x ↦ by simp [smul_comm r]
  left_inv f := (DGTwistedObject.dgHomEquiv R _ _ n).injective <|
    DGAdditiveClosure.dgHom_ext R fun x u ↦ shiftCoeff_injective <| by
      simp [smul_smul]
  right_inv g := Subtype.ext <| funext fun x ↦ by
    simp [smul_smul]

private theorem homEquiv_apply (n : ℤ)
    (f : DGHom R n (m.toDGTwistedObject h) (starTwistedObject h)) (x : P) :
    (homEquiv m n f : P → A) x = ((n + 1) * ind x).negOnePow • shiftCoeff
      (DGAdditiveClosure.dgHomEquiv R _ _ n (DGTwistedObject.dgHomEquiv R _ _ n f) x PUnit.unit) :=
  (rfl)

/-- Under `homEquiv`, the twisted differential of the Hom complex `T_m ⟶ ⋆[0]` is the twisted
differential of `K_m`. -/
private theorem homEquiv_dgDifferential (n : ℤ)
    (f : DGHom R n (m.toDGTwistedObject h) (starTwistedObject h)) :
    (homEquiv m (n + 1) (dgDifferential R n f) : P → A) =
      twistedDifferential m.m 𝒜 d (homEquiv m n f) := by
  funext x
  have hg (y : P) : (homEquiv m n f : P → A) y ∈ 𝒜 (n + ind y) :=
    mem_twistedTotalGrading_iff.1 (homEquiv m n f).property y
  -- Expand both sides at `x` into elements of `A`: on the left, the twisted differential of the
  -- Hom complex, where the twist of `⋆[0]` vanishes; on the right, that of `K_m`.
  rw [homEquiv_apply, twistedDifferential_apply, DGTwistedObject.dgHomEquiv_dgDifferential]
  simp only [fun y ↦ koszulTwist_one_eq_negOnePow_smul (R := R) (hg y)]
  simp only [homEquiv_apply, dgComp_zero, smul_zero, add_zero, map_sub, Pi.sub_apply]
  rw [DGAdditiveClosure.dgHomEquiv_dgDifferential, DGAdditiveClosure.dgHomEquiv_dgComp,
    shiftCoeff_dgDifferential, map_sum]
  have ht (y : P) : shiftCoeff (DGAdditiveClosure.dgHomEquiv R _ _ 1
      (twistMatrix (h := h) m.m m.mem_graded) x y) = -m.m y x :=
    shiftCoeff_twistMatrix _ _ x y
  simp only [shiftCoeff_dgComp, ht]
  -- Match the differential term and the sum termwise, up to a sign identity.
  rw [map_zsmul_unit, smul_sub, Finset.smul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib,
    smul_smul]
  congr 1
  · congr 1
    rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨ind x, by ring⟩
  · refine Finset.sum_congr rfl fun y _ ↦ ?_
    simp only [op_smul_eq_mul, smul_mul_assoc, mul_neg, smul_neg, neg_neg, smul_smul]
    congr 1
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨n * ind x + ind x + ind x * ind y - ind y * n - ind y * ind y, by ring⟩

/-- **The twisted complex `K_m` is the Hom complex `T_m ⟶ ⋆[0]`.** For a twisting cocycle `m`, the
Hom complex from the twisted object `T_m = (⊕_x ⋆[-ind x], -mᵀ)` to `⋆[0]`, with its twisted
differential, is isomorphic to the twisted complex `K_m` of the free rank-one module `A`: in
degree `n`, a morphism with components `f_x : ⋆[-ind x] ⟶ ⋆[0]` goes to the function
`x ↦ (-1)^((n + 1) * ind x) • f_x` of total degree `n`
(`TauCeti.TwistingCocycle.dgHomComplexIso_hom_f_apply`). So `K_m`, with `x` in degree `-ind x` and
`d x = Σ_y m x y · y`, is the twisted complex of shifted free modules with transposed matrix
`-mᵀ`. -/
noncomputable def dgHomComplexIso :
    dgHomComplex R (m.toDGTwistedObject h) (starTwistedObject h) ≅
      m.twistedCochainComplex d h.isDGRightModule :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((homEquiv m n).trans (twistedCochainComplexXEquiv m.mem_graded m.twisting
      h.isDGRightModule n).symm).toModuleIso) <| by
    rintro n _ rfl
    ext f
    apply (twistedCochainComplexXEquiv m.mem_graded m.twisting h.isDGRightModule (n + 1)).injective
    apply Subtype.ext
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.toModuleIso_hom, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      ModuleCat.hom_ofHom, twistedCochainComplexXEquiv_d, LinearEquiv.apply_symm_apply]
    exact (homEquiv_dgDifferential m n f).symm

/-- The isomorphism `TauCeti.TwistingCocycle.dgHomComplexIso` sends a degree-`n` morphism
`T_m ⟶ ⋆[0]` to the function whose value at `x` is `(-1)^((n + 1) * ind x)` times the element of
`A` underlying its component `⋆[-ind x] ⟶ ⋆[0]`. -/
theorem dgHomComplexIso_hom_f_apply (n : ℤ)
    (f : DGHom R n (m.toDGTwistedObject h) (starTwistedObject h)) (x : P) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting h.isDGRightModule n
        (((dgHomComplexIso m).hom.f n).hom f) : P → A) x =
      ((n + 1) * ind x).negOnePow • shiftCoeff (DGAdditiveClosure.dgHomEquiv R _ _ n
        (DGTwistedObject.dgHomEquiv R _ _ n f) x PUnit.unit) := by
  simp [dgHomComplexIso, homEquiv_apply]

end TwistingCocycle

end TauCeti
