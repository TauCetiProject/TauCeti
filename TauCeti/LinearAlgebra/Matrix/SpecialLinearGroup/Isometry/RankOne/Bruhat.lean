/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.RankOne
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.RankOne.RootAction
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.RankOne.Basic
import TauCeti.LinearAlgebra.Projectivization.Action

/-!
# The Bruhat decomposition and split Tits system of the rank-one unitary group

Let `σ` be an involution of a field `K` and let `G` be the group of determinant-one isometries of
the signed reversal form `Q = !![0, 0, 1; 0, -1, 0; 1, 0, 0]` relative to `σ`
(`TauCeti.UnitaryRankOne.Group`). Over the field with `q²` elements and `σ(x) = x ^ q` this is
`SU₃(q)`, whose derived subgroup modulo its centre is the twisted group `²A₂(q)`. The group acts
on the isotropic points of the projective plane, which are the point at infinity `[1 : 0 : 0]`
and the affine points `[z : x : 1]` with `z + σ(z) = σ(x) x`
(`TauCeti.UnitaryRankOne.isotropicPointsEquiv`).

This file builds the split Tits system of rank one of `G`:

* the **Borel subgroup** `B` is the stabilizer of the point at infinity. It is the product of
  the diagonal torus `T` and the **unipotent subgroup** `U` of upper unitriangular isometries,
  the image of the unitary Heisenberg group (`TauCeti.HeisenbergGroup.unitarySubgroup`);
* the **monomial subgroup** `N` consists of the torus and its translate by the signed reversal
  Weyl representative `w`, and `B ∩ N = T`.

The unipotent subgroup acts simply transitively on the affine isotropic points: the root element
with parameters `(x, z)` sends `[0 : 0 : 1] = w [1 : 0 : 0]` to `[z : σ(x) : 1]`
(`TauCeti.UnitaryRankOne.upperRootHom_smul_origin`). Hence every
element of `G` outside `B` lies in `U w B`, which is the **Bruhat decomposition**
`G = B ∪ B w B`. Since a nontrivial element of `U` moves `[0 : 0 : 1]`, its conjugate by `w` lies
outside `B`, and no nontrivial element of `U` lies in every conjugate of `B`. Together with
`TauCeti.TitsSystem.ofRankOne` this gives an irreducible Tits system on `G`, and supplies the
hypotheses on `U` of Tits's simplicity criterion
`TauCeti.TitsSystem.isSimpleGroup_derivedCentralQuotient`: `U` is solvable, normalized by `B`,
`B ≤ U (B ∩ N)`, and `U` meets the normal core of `B` trivially. That criterion additionally needs
the normal closure of `U` to be the derived subgroup of `G` and perfect, which is not proved here.

Everything holds over every field with an involution, including in characteristic two.

## Main definitions

* `TauCeti.UnitaryRankOne.unipotent`: the upper unitriangular isometries.
* `TauCeti.UnitaryRankOne.borel`: the stabilizer of the point at infinity.
* `TauCeti.UnitaryRankOne.monomial`: the torus together with its translate by `w`.
* `TauCeti.UnitaryRankOne.titsSystem`: the Tits system `(B, N)` of rank one.

## Main results

* `TauCeti.UnitaryRankOne.borel_eq_unipotent_sup_torus`: `B = U T`.
* `TauCeti.UnitaryRankOne.exists_eq_unipotent_mul_weyl_mul`: every element outside `B` lies in
  `U w B`.
* `TauCeti.UnitaryRankOne.mem_borel_or_mem_doubleCoset`: the Bruhat decomposition `G = B ∪ BwB`.
* `TauCeti.UnitaryRankOne.borel_inf_monomial`: `B ∩ N = T`.
* `TauCeti.UnitaryRankOne.borel_le_unipotent_sup_borel_inf_monomial`: `B ≤ U (B ∩ N)`.
* `TauCeti.UnitaryRankOne.normalCore_borel_inf_unipotent`: `U` meets the normal core of `B`
  trivially.
* `TauCeti.UnitaryRankOne.isIrreducible_titsSystem`: the Tits system is irreducible.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), Chapter 13.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 10.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 29.1.
-/

public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace TauCeti.UnitaryRankOne

/-! ### The unipotent subgroup -/

section CommRing

variable (R : Type*) [CommRing R] (σ : R →+* R)

/-- The **unipotent subgroup**: the image of the unitary Heisenberg group, which consists of the
upper unitriangular isometries (`TauCeti.UnitaryRankOne.mem_unipotent_iff`). -/
def unipotent : Subgroup (UnitaryRankOne.Group R σ) :=
  (upperRootHom R σ).range

variable {R σ} in
/-- An isometry is unipotent exactly when it is a root element. -/
theorem mem_unipotent_iff_exists {g : UnitaryRankOne.Group R σ} :
    g ∈ unipotent R σ ↔ ∃ a, upperRootHom R σ a = g :=
  Iff.rfl

/-- Every root element is unipotent. -/
@[simp]
theorem upperRootHom_mem_unipotent (a : HeisenbergGroup.unitarySubgroup σ) :
    upperRootHom R σ a ∈ unipotent R σ :=
  mem_unipotent_iff_exists.mpr ⟨a, rfl⟩

variable {R σ} in
/-- An isometry lies in the unipotent subgroup exactly when its matrix is upper unitriangular. -/
theorem mem_unipotent_iff (g : UnitaryRankOne.Group R σ) :
    g ∈ unipotent R σ ↔
      ((g : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).IsUpperUnitriangular :=
  mem_range_upperRootHom_iff g

/-- The unipotent subgroup is solvable, being a quotient of a subgroup of the nilpotent Heisenberg
group. -/
instance : Group.IsSolvable (unipotent R σ) :=
  Group.isSolvable_of_surjective (upperRootHom R σ).rangeRestrict_surjective

variable {σ} in
/-- The unipotent subgroup is nontrivial over a nontrivial commutative ring. -/
theorem unipotent_ne_bot [Nontrivial R] (hσ : Function.Involutive σ) : unipotent R σ ≠ ⊥ := by
  have := HeisenbergGroup.nontrivial_unitarySubgroup hσ
  obtain ⟨a, ha⟩ := exists_ne (1 : HeisenbergGroup.unitarySubgroup σ)
  rw [Ne, Subgroup.eq_bot_iff_forall, not_forall]
  exact ⟨_, not_imp.mpr ⟨upperRootHom_mem_unipotent R σ a,
    (map_ne_one_iff _ (upperRootHom_injective R σ)).mpr ha⟩⟩

/-- An element of the torus conjugates the unipotent subgroup into itself. -/
private theorem mul_mul_inv_mem_unipotent {t u : UnitaryRankOne.Group R σ} (ht : t ∈ torus R σ)
    (hu : u ∈ unipotent R σ) : t * u * t⁻¹ ∈ unipotent R σ := by
  rw [mem_unipotent_iff] at hu ⊢
  have hD := ((mem_torus_iff R σ t).mp ht).diagonal_diag
  have hE := ((mem_torus_iff R σ _).mp (inv_mem ht)).diagonal_diag
  have hDE : ((t : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) *
      ((t⁻¹ : UnitaryRankOne.Group R σ) : SpecialLinearGroup (Fin 3) R) = 1 := by
    rw [← coe_mul, mul_inv_cancel, coe_one]
  rw [← hD, ← hE, diagonal_mul_diagonal] at hDE
  have key := hu.diagonal_mul_mul_diagonal
    (d := ((t : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).diag)
    (e := (((t⁻¹ : UnitaryRankOne.Group R σ) : SpecialLinearGroup (Fin 3) R) :
      Matrix (Fin 3) (Fin 3) R).diag) fun i ↦ by
    simpa using congrFun (congrFun hDE i) i
  rw [hD, hE] at key
  rwa [coe_mul, coe_mul]

/-- The torus normalizes the unipotent subgroup. -/
theorem torus_le_normalizer_unipotent :
    torus R σ ≤ Subgroup.normalizer (unipotent R σ : Set (UnitaryRankOne.Group R σ)) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  refine fun u ↦ ⟨mul_mul_inv_mem_unipotent R σ ht, fun hu ↦ ?_⟩
  simpa [mul_assoc] using mul_mul_inv_mem_unipotent R σ (inv_mem ht) hu

/-! ### The monomial subgroup -/

/-- The **monomial subgroup**: the torus `T` together with its translate `w T` by the Weyl
representative `w`. -/
def monomial : Subgroup (UnitaryRankOne.Group R σ) where
  carrier := {g | g ∈ torus R σ ∨ weyl R σ * g ∈ torus R σ}
  one_mem' := Or.inl (one_mem _)
  mul_mem' := by
    rintro g h (hg | hg) (hh | hh)
    · exact Or.inl (mul_mem hg hh)
    · exact Or.inr (by simpa [mul_assoc] using mul_mem (weyl_mul_mul_weyl_mem_torus hg) hh)
    · exact Or.inr (by simpa [mul_assoc] using mul_mem hg hh)
    · exact Or.inl (by simpa [mul_assoc] using mul_mem (weyl_mul_mul_weyl_mem_torus hg) hh)
  inv_mem' := by
    rintro g (hg | hg)
    · exact Or.inl (inv_mem hg)
    · exact Or.inr (by simpa [mul_assoc] using weyl_mul_mul_weyl_mem_torus (inv_mem hg))

variable {R σ} in
/-- An element is monomial exactly when it or its product with the Weyl representative is in the
torus. -/
theorem mem_monomial_iff {g : UnitaryRankOne.Group R σ} :
    g ∈ monomial R σ ↔ g ∈ torus R σ ∨ weyl R σ * g ∈ torus R σ :=
  Iff.rfl

/-- The torus is contained in the monomial subgroup. -/
theorem torus_le_monomial : torus R σ ≤ monomial R σ := fun _ ↦ Or.inl

/-- The Weyl representative is monomial. -/
theorem weyl_mem_monomial : weyl R σ ∈ monomial R σ :=
  Or.inr (by simpa only [weyl_mul_self] using one_mem (torus R σ))

/-- The monomial subgroup normalizes the torus. -/
theorem monomial_le_normalizer_torus :
    monomial R σ ≤ Subgroup.normalizer (torus R σ : Set (UnitaryRankOne.Group R σ)) := by
  rintro g (hg | hg)
  · exact Subgroup.le_normalizer hg
  · simpa using mul_mem (weyl_mem_normalizer_torus R σ) (Subgroup.le_normalizer hg)

end CommRing

/-! ### The Borel subgroup -/

variable (K : Type*) [Field K] (σ : K →+* K)

/-- The **Borel subgroup**: the stabilizer of the isotropic point at infinity `[1 : 0 : 0]`. -/
def borel : Subgroup (UnitaryRankOne.Group K σ) :=
  MulAction.stabilizer _ (infinity K σ)

variable {K σ}

/-- An isometry lies in the Borel subgroup exactly when it fixes the point at infinity. -/
theorem mem_borel_iff_smul_infinity {g : UnitaryRankOne.Group K σ} :
    g ∈ borel K σ ↔ g • infinity K σ = infinity K σ :=
  MulAction.mem_stabilizer_iff

/-- An element sending a representative of `p` to a multiple of a representative of `q` sends
`p` to `q`. -/
private theorem smul_eq_of_mulVec_eq_smul {g : UnitaryRankOne.Group K σ}
    {p q : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ}
    {v w : Fin 3 → K} (hv : v ≠ 0) (hw : w ≠ 0)
    (hp : (p : ℙ K (Fin 3 → K)) = Projectivization.mk K v hv)
    (hq : (q : ℙ K (Fin 3 → K)) = Projectivization.mk K w hw) (c : K)
    (h : ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • w) :
    g • p = q := by
  apply Subtype.ext
  rw [SubMulAction.val_smul, hp, hq]
  exact TauCeti.Projectivization.smul_mk_eq_mk_of_smul_eq_smul hv hw (c := c)
    (by rw [smul_def, h])

/-- Conversely, an element sending `p` to `q` sends a representative of `p` to a multiple of a
representative of `q`. -/
private theorem exists_mulVec_eq_smul_of_smul_eq {g : UnitaryRankOne.Group K σ}
    {p q : (typeAGraphConjugator 2 K : Matrix (Fin 3) (Fin 3) K).isotropicPoints σ}
    {v w : Fin 3 → K} (hv : v ≠ 0) (hw : w ≠ 0)
    (hp : (p : ℙ K (Fin 3 → K)) = Projectivization.mk K v hv)
    (hq : (q : ℙ K (Fin 3 → K)) = Projectivization.mk K w hw) (h : g • p = q) :
    ∃ c : K, ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • w := by
  have h := congrArg Subtype.val h
  rw [SubMulAction.val_smul, hp, hq, Subgroup.smul_def, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨c, hc⟩ := h
  -- The projective action goes through the special linear group, whose action on vectors is the
  -- action of `g` itself.
  exact ⟨c, by rw [← smul_def, Subgroup.smul_def, hc]⟩

variable (K σ) in
/-- The Weyl representative sends the point at infinity to `[0 : 0 : 1]`. -/
@[simp]
theorem weyl_smul_infinity : weyl K σ • infinity K σ = origin K σ :=
  smul_eq_of_mulVec_eq_smul _ _ (coe_infinity K σ) (coe_origin K σ) 1
    (by simp [coe_typeAGraphConjugator_two, funext_iff, Fin.forall_fin_succ])

/-- An isometry fixes the point at infinity exactly when its first column is a multiple of the
first basis vector. -/
theorem mem_borel_iff (g : UnitaryRankOne.Group K σ) :
    g ∈ borel K σ ↔
      ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
        ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  -- The point at infinity is spanned by the first basis vector.
  have he : (![1, 0, 0] : Fin 3 → K) = Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := exists_mulVec_eq_smul_of_smul_eq _ _ (coe_infinity K σ) (coe_infinity K σ)
      (mem_borel_iff_smul_infinity.mp hg)
    rw [he, mulVec_single_one] at hc
    exact ⟨by simpa using congrFun hc 1, by simpa using congrFun hc 2⟩
  · rintro ⟨h₁, h₂⟩
    refine mem_borel_iff_smul_infinity.mpr (smul_eq_of_mulVec_eq_smul _ _ (coe_infinity K σ)
      (coe_infinity K σ) (((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) ?_)
    rw [he, mulVec_single_one]
    ext i
    fin_cases i <;> simp [h₁, h₂]

variable (K σ)

/-- The unipotent subgroup fixes the point at infinity. -/
theorem unipotent_le_borel : unipotent K σ ≤ borel K σ := fun u hu ↦ by
  obtain ⟨hu, -⟩ := (isUpperUnitriangular_def _).mp ((mem_unipotent_iff u).mp hu)
  exact (mem_borel_iff u).mpr ⟨hu (by decide), hu (by decide)⟩

/-- The torus fixes the point at infinity. -/
theorem torus_le_borel : torus K σ ≤ borel K σ := fun t ht ↦ by
  have ht := (mem_torus_iff K σ t).mp ht
  exact (mem_borel_iff t).mpr ⟨ht (by decide), ht (by decide)⟩

/-- The Weyl representative moves the point at infinity. -/
theorem weyl_notMem_borel : weyl K σ ∉ borel K σ := fun h ↦
  point_ne_infinity _ ((origin_eq_point K σ).symm.trans
    ((weyl_smul_infinity K σ).symm.trans (mem_borel_iff_smul_infinity.mp h)))

variable {K σ}

/-- An element of the Borel subgroup with top left entry one is upper unitriangular. -/
private theorem mem_unipotent_of_mem_borel {g : UnitaryRankOne.Group K σ} (hg : g ∈ borel K σ)
    (h₀₀ : ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1) :
    g ∈ unipotent K σ := by
  obtain ⟨h₁₀, h₂₀⟩ := (mem_borel_iff g).mp hg
  -- The first row of the isometry equation reads off the last row of `g`, and the determinant
  -- then gives the middle diagonal entry.
  have hiso := mem_specialIsometryGroup_iff.mp g.property
  have h₂₁ : ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    simpa [coe_typeAGraphConjugator_two, Matrix.mul_apply, Fin.sum_univ_three, h₁₀, h₂₀, h₀₀]
      using congrFun (congrFun hiso 0) 1
  have h₂₂ : ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    simpa [coe_typeAGraphConjugator_two, Matrix.mul_apply, Fin.sum_univ_three, h₁₀, h₂₀, h₀₀]
      using congrFun (congrFun hiso 0) 2
  have hdet := (g : SpecialLinearGroup (Fin 3) K).det_coe
  rw [det_fin_three, h₁₀, h₂₀, h₀₀, h₂₁, h₂₂] at hdet
  have h₁₁ : ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    linear_combination hdet
  rw [mem_unipotent_iff, isUpperUnitriangular_def]
  refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> simp_all

/-- **The Levi decomposition of the Borel subgroup**: `B = U T`. -/
theorem borel_eq_unipotent_sup_torus (hσ : Function.Involutive σ) :
    borel K σ = unipotent K σ ⊔ torus K σ := by
  refine le_antisymm (fun g hg ↦ ?_) (sup_le (unipotent_le_borel K σ) (torus_le_borel K σ))
  obtain ⟨h₁₀, h₂₀⟩ := (mem_borel_iff g).mp hg
  have ha : ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro ha
    have hdet := (g : SpecialLinearGroup (Fin 3) K).det_coe
    rw [det_fin_three, h₁₀, h₂₀, ha] at hdet
    simp at hdet
  -- Divide `g` by the torus element with the same top left entry.
  have ht := torusHom_mem_torus K σ hσ (Units.mk0 _ ha)
  have hu : (torusHom K σ hσ (Units.mk0 _ ha))⁻¹ * g ∈ unipotent K σ := by
    refine mem_unipotent_of_mem_borel (mul_mem (inv_mem (torus_le_borel K σ ht)) hg) ?_
    simp [← map_inv, diagonal_mul, ha]
  simpa using mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hu)

/-- The Borel subgroup normalizes the unipotent subgroup. -/
theorem borel_le_normalizer_unipotent (hσ : Function.Involutive σ) :
    borel K σ ≤ Subgroup.normalizer (unipotent K σ : Set (UnitaryRankOne.Group K σ)) := by
  rw [borel_eq_unipotent_sup_torus hσ]
  exact sup_le Subgroup.le_normalizer (torus_le_normalizer_unipotent K σ)

/-! ### The Bruhat decomposition -/

/-- **The big cell.** Every element of the rank-one unitary group outside the Borel subgroup is
`u w b` for a unipotent `u` and an element `b` of the Borel subgroup. -/
theorem exists_eq_unipotent_mul_weyl_mul (hσ : Function.Involutive σ)
    {g : UnitaryRankOne.Group K σ} (hg : g ∉ borel K σ) :
    ∃ u ∈ unipotent K σ, ∃ b ∈ borel K σ, g = u * weyl K σ * b := by
  -- Some root element sends `[0 : 0 : 1] = w [1 : 0 : 0]` to `g [1 : 0 : 0]`.
  obtain ⟨a, ha, -⟩ := existsUnique_upperRootHom_smul_origin hσ (g • infinity K σ)
    fun h ↦ hg (mem_borel_iff_smul_infinity.mpr h)
  refine ⟨upperRootHom K σ a, upperRootHom_mem_unipotent K σ a,
    (upperRootHom K σ a * weyl K σ)⁻¹ * g, ?_, by group⟩
  rw [mem_borel_iff_smul_infinity, mul_smul, inv_smul_eq_iff, mul_smul, weyl_smul_infinity, ha]

/-- **The Bruhat decomposition** `G = B ∪ B w B` of the rank-one unitary group. -/
theorem mem_borel_or_mem_doubleCoset (hσ : Function.Involutive σ) (g : UnitaryRankOne.Group K σ) :
    g ∈ borel K σ ∨ g ∈ DoubleCoset.doubleCoset (weyl K σ) (borel K σ) (borel K σ) := by
  refine or_iff_not_imp_left.mpr fun hg ↦ ?_
  obtain ⟨u, hu, b, hb, rfl⟩ := exists_eq_unipotent_mul_weyl_mul hσ hg
  exact DoubleCoset.mem_doubleCoset.mpr ⟨u, unipotent_le_borel K σ hu, b, hb, rfl⟩

/-- The conjugate of a unipotent element by the Weyl representative fixes the point at infinity
exactly when the element is trivial. -/
theorem weyl_mul_mul_weyl_mem_borel_iff {u : UnitaryRankOne.Group K σ} (hu : u ∈ unipotent K σ) :
    weyl K σ * u * weyl K σ ∈ borel K σ ↔ u = 1 := by
  obtain ⟨a, rfl⟩ := mem_unipotent_iff_exists.mp hu
  rw [mem_borel_iff_smul_infinity, mul_smul, mul_smul, weyl_smul_infinity,
    smul_eq_iff_eq_inv_smul, weyl_inv, weyl_smul_infinity, origin_eq_point,
    upperRootHom_smul_eq_self_iff _ _ (point_ne_infinity _),
    map_eq_one_iff _ (upperRootHom_injective K σ)]

variable (K σ) in
/-- **The unipotent subgroup meets the normal core of the Borel subgroup trivially.** -/
theorem normalCore_borel_inf_unipotent : (borel K σ).normalCore ⊓ unipotent K σ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun u ⟨hZ, hu⟩ ↦ ?_
  have h : weyl K σ * u * (weyl K σ)⁻¹ ∈ borel K σ := hZ (weyl K σ)
  rwa [weyl_inv, weyl_mul_mul_weyl_mem_borel_iff hu] at h

/-! ### The Tits system -/

/-- **The Borel and monomial subgroups meet in the torus.** -/
theorem borel_inf_monomial : borel K σ ⊓ monomial K σ = torus K σ := by
  refine le_antisymm (fun g ⟨hgB, hgN⟩ ↦ ?_)
    (le_inf (torus_le_borel K σ) (torus_le_monomial K σ))
  refine (mem_monomial_iff.mp hgN).resolve_right fun h ↦ weyl_notMem_borel K σ ?_
  simpa using mul_mem (torus_le_borel K σ h) (inv_mem hgB)

/-- The Borel subgroup is contained in the product of the unipotent subgroup and its intersection
with the monomial subgroup: the splitting hypothesis of
`TauCeti.TitsSystem.isSimpleGroup_derivedCentralQuotient`. -/
theorem borel_le_unipotent_sup_borel_inf_monomial (hσ : Function.Involutive σ) :
    borel K σ ≤ unipotent K σ ⊔ borel K σ ⊓ monomial K σ := by
  rw [borel_inf_monomial]
  exact (borel_eq_unipotent_sup_torus hσ).le

/-- The intersection of the Borel and monomial subgroups, the torus, is normal in the monomial
subgroup. -/
instance : ((borel K σ).subgroupOf (monomial K σ)).Normal := by
  rw [← Subgroup.inf_subgroupOf_right, borel_inf_monomial]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (torus_le_monomial K σ)).mpr
    (monomial_le_normalizer_torus K σ)

variable (K) in
/-- **The Tits system of the rank-one unitary group**, with the Borel subgroup `B`, the monomial
subgroup `N` and the single simple reflection given by the Weyl representative. Its Bruhat
decomposition is `TauCeti.UnitaryRankOne.mem_borel_or_mem_doubleCoset`. -/
def titsSystem (hσ : Function.Involutive σ) : TitsSystem (UnitaryRankOne.Group K σ) :=
  TitsSystem.ofRankOne (borel K σ) (monomial K σ) ⟨weyl K σ, weyl_mem_monomial K σ⟩
    (by simp [one_mem])
    (fun _ hx ↦ (mem_monomial_iff.mp hx).imp (fun h ↦ torus_le_borel K σ h)
      fun h ↦ by simpa using torus_le_borel K σ h)
    (by
      obtain ⟨⟨u, hu⟩, hu₁⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (unipotent_ne_bot K hσ)
      refine ⟨u, unipotent_le_borel K σ hu, ?_⟩
      rw [Subgroup.coe_mk, weyl_inv, weyl_mul_mul_weyl_mem_borel_iff hu]
      exact fun h ↦ hu₁ (Subtype.ext h))
    (mem_borel_or_mem_doubleCoset hσ)

/-- The Borel subgroup of the Tits system is the stabilizer of the point at infinity. -/
@[simp]
theorem titsSystem_subgroupB (hσ : Function.Involutive σ) :
    (titsSystem K hσ).subgroupB = borel K σ := by
  unfold titsSystem
  exact TitsSystem.ofRankOne_subgroupB

/-- The subgroup `N` of the Tits system is the monomial subgroup. -/
@[simp]
theorem titsSystem_subgroupN (hσ : Function.Involutive σ) :
    (titsSystem K hσ).subgroupN = monomial K σ := by
  unfold titsSystem
  exact TitsSystem.ofRankOne_subgroupN

/-- The only simple reflection of the Tits system is the class of the Weyl representative. -/
@[simp]
theorem titsSystem_simple (hσ : Function.Involutive σ) :
    (titsSystem K hσ).simple =
      {QuotientGroup.mk ⟨weyl K σ, by simpa using weyl_mem_monomial K σ⟩} := by
  unfold titsSystem
  exact TitsSystem.ofRankOne_simple

/-- **The Tits system of the rank-one unitary group is irreducible.** -/
theorem isIrreducible_titsSystem (hσ : Function.Involutive σ) :
    (titsSystem K hσ).IsIrreducible := by
  unfold titsSystem
  exact TitsSystem.isIrreducible_ofRankOne

end TauCeti.UnitaryRankOne
