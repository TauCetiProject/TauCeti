/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.Algebra.Group.Submonoid.Saturation
public import TauCeti.Geometry.Convex.Cone.Saturation
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Lift
import TauCeti.Geometry.Convex.Cone.Alternative
import TauCeti.Geometry.Convex.Cone.Face.Exposed
import TauCeti.Geometry.Convex.Cone.Face.Finite

/-!
# Comparison of cone faces and semigroup faces

Faces of an additive monoid `S` are bundled in Mathlib as `SaturatedAddSubmonoid S`, while faces of
a pointed cone `C : PointedCone R V` are bundled as `C.Face`. This file compares the two face
lattices:

1. Over any ordered semiring `R`, restricting a face of `C` to `C` itself defines an order
   embedding `PointedCone.faceOrderEmbeddingSaturatedAddSubmonoid`, and pulling back along
   `i : M →+ V` defines an order embedding `PointedCone.hullFaceOrderEmbedding` into
   `SaturatedAddSubmonoid S` without any injectivity or finite-generation assumptions.
2. Over `ℚ`, every saturated additive submonoid of a pointed cone `C : PointedCone ℚ V` spans a
   face of `C` (`PointedCone.faceOrderIsoSaturatedAddSubmonoid`), and for any injective additive
   homomorphism `i : M →+ V` into a `ℚ`-module and any additive submonoid `S : AddSubmonoid M`
   (not necessarily finitely generated), `PointedCone.hullRatFaceOrderIso` upgrades
   `hullFaceOrderEmbedding` to an order isomorphism
   `(PointedCone.hull ℚ (i '' S)).Face ≃o SaturatedAddSubmonoid S`.
3. For a finitely generated submonoid `S` of a free abelian group `L`, Tucker's theorem over `ℤ`
   exposes every semigroup face `F : SaturatedAddSubmonoid S` by an integral linear functional
   `m : L →+ ℤ` nonnegative on `S` and vanishing on `S` precisely along `F`
   (`SaturatedAddSubmonoid.exists_addMonoidHom_nonneg_and_eq_zero_iff`). Consequently, over any
   strictly ordered commutative ring `R` (such as `ℝ`, `ℚ`, or `ℤ`), whenever `ℤ`-linear
   functionals on `L` extend along `i : L →+ V` to `Module.Dual R V` — in particular for scalar
   extension `L → R ⊗[ℤ] L` — cone faces of `PointedCone.hull R (i '' S)` correspond
   order-isomorphically to semigroup faces of `S` (`PointedCone.hullFaceOrderIsoOfDualExt` and
   `PointedCone.hullBaseChangeFaceOrderIso`).

## Main declarations

* `PointedCone.faceOrderEmbeddingSaturatedAddSubmonoid` and `PointedCone.hullFaceOrderEmbedding`:
  order embeddings from cone faces to monoid faces over an arbitrary ordered semiring.
* `PointedCone.faceOrderIsoSaturatedAddSubmonoid` and `PointedCone.hullRatFaceOrderIso`:
  unconditional order isomorphisms `C.Face ≃o SaturatedAddSubmonoid C` and
  `(PointedCone.hull ℚ (i '' S)).Face ≃o SaturatedAddSubmonoid S` over `ℚ`.
* `SaturatedAddSubmonoid.exists_addMonoidHom_nonneg_and_eq_zero_iff` and
  `SaturatedAddSubmonoid.exists_addMonoidHom_closure_nonneg_and_eq_zero_iff`: integral linear
  exposure of faces of finitely generated submonoids of free or torsion-free abelian groups.
* `PointedCone.hullFaceOrderIsoOfDualExt` and `PointedCone.hullBaseChangeFaceOrderIso`: order
  isomorphism `(PointedCone.hull R (i '' S)).Face ≃o SaturatedAddSubmonoid S` for finitely
  generated submonoids over any strictly ordered commutative ring `R`.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Proposition 2.13 and Theorem 2.10.
* E. Miller and B. Sturmfels, *Combinatorial Commutative Algebra*, Theorem 7.8.
* W. Fulton, *Introduction to Toric Varieties*, §1.2.
-/

public section

namespace PointedCone

section OrderedSemiring

variable {R M V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid M] [AddCommGroup V] [Module R V]

/-- Every face of a pointed cone `C` cuts out a saturated additive submonoid of `C`, giving an
order embedding `C.Face ↪o SaturatedAddSubmonoid C`. -/
def faceOrderEmbeddingSaturatedAddSubmonoid (C : PointedCone R V) :
    C.Face ↪o SaturatedAddSubmonoid C :=
  OrderEmbedding.ofMapLEIff
    (fun τ ↦
      { toAddSubmonoid := τ.toAddSubmonoid.comap C.toAddSubmonoid.subtype
        addSaturated {x y} hxy := (τ.isFaceOf.add_mem_iff_mem x.property y.property).1 hxy })
    fun τ₁ _ ↦ ⟨fun h v hv ↦ @h ⟨v, τ₁.toPointedCone_le hv⟩ hv, fun h _ hx ↦ h hx⟩

/-- Membership in `C.faceOrderEmbeddingSaturatedAddSubmonoid τ` is membership of the underlying
vector in `τ`. -/
@[simp]
theorem mem_faceOrderEmbeddingSaturatedAddSubmonoid {C : PointedCone R V} (τ : C.Face) (x : C) :
    x ∈ C.faceOrderEmbeddingSaturatedAddSubmonoid τ ↔ (x : V) ∈ τ :=
  Iff.rfl

variable (R) in
/-- Canonical additive monoid homomorphism from `S : AddSubmonoid M` into the pointed cone hull
`PointedCone.hull R (i '' (S : Set M))` along `i : M →+ V`. -/
def toHull (i : M →+ V) (S : AddSubmonoid M) :
    S →+ PointedCone.hull R (i '' (S : Set M)) where
  toFun s := ⟨i s.val, PointedCone.subset_hull ⟨s.val, s.property, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero i)
  map_add' a b := Subtype.ext (map_add i a.val b.val)

variable (R) in
/-- `PointedCone.toHull` sends `s : S` to `i s` in the ambient module `V`. -/
@[simp]
theorem coe_toHull (i : M →+ V) (S : AddSubmonoid M) (s : S) :
    (toHull R i S s : V) = i s.val :=
  (rfl)

variable (R) in
/-- `PointedCone.toHull` is injective whenever `i` is injective. -/
theorem toHull_injective {i : M →+ V} (hi : Function.Injective i) (S : AddSubmonoid M) :
    Function.Injective (toHull R i S) :=
  fun _ _ h ↦ Subtype.ext (hi (congrArg Subtype.val h))

variable (R) in
/-- Pulling back faces of `PointedCone.hull R (i '' (S : Set M))` along `i` embeds its face lattice
into the lattice `SaturatedAddSubmonoid S` of monoid faces of `S`. -/
def hullFaceOrderEmbedding (i : M →+ V) (S : AddSubmonoid M) :
    (PointedCone.hull R (i '' (S : Set M))).Face ↪o SaturatedAddSubmonoid S :=
  OrderEmbedding.ofMapLEIff
    (fun τ ↦
      ((PointedCone.hull R (i '' (S : Set M))).faceOrderEmbeddingSaturatedAddSubmonoid τ).comap
        (toHull R i S))
    fun {τ₁ τ₂} ↦ by
      refine ⟨fun h ↦ ?_, fun h s hs ↦ ?_⟩
      · have hτ₁ : τ₁.toPointedCone = PointedCone.hull R ((i '' (S : Set M)) ∩ τ₁) :=
          τ₁.isFaceOf.eq_hull_inter_of_eq_hull rfl
        rw [← Face.toPointedCone_le_toPointedCone, hτ₁]
        refine Submodule.span_le.2 ?_
        rintro _ ⟨⟨x, hxS, rfl⟩, hx⟩
        have hx' := @h ⟨x, hxS⟩
        simp only [SaturatedAddSubmonoid.mem_comap,
          mem_faceOrderEmbeddingSaturatedAddSubmonoid, coe_toHull] at hx'
        exact hx' hx
      · simp only [SaturatedAddSubmonoid.mem_comap,
          mem_faceOrderEmbeddingSaturatedAddSubmonoid, coe_toHull] at hs ⊢
        exact h hs

/-- An element `s : S` belongs to `hullFaceOrderEmbedding R i S τ` iff `i s ∈ τ`. -/
@[simp]
theorem mem_hullFaceOrderEmbedding {i : M →+ V} {S : AddSubmonoid M}
    (τ : (PointedCone.hull R (i '' (S : Set M))).Face) (s : S) :
    s ∈ hullFaceOrderEmbedding R i S τ ↔ i s.val ∈ τ := by
  simp [hullFaceOrderEmbedding]

/-- Any cone face `τ` of `PointedCone.hull R (i '' S)` whose pullback to `S` equals `F` is the cone
hull of the image of `F`. -/
theorem toPointedCone_eq_hull_image_of_hullFaceOrderEmbedding_eq {i : M →+ V} {S : AddSubmonoid M}
    {τ : (PointedCone.hull R (i '' (S : Set M))).Face} {F : SaturatedAddSubmonoid S}
    (h : hullFaceOrderEmbedding R i S τ = F) :
    τ.toPointedCone = PointedCone.hull R ((i ∘ S.subtype) '' (F : Set S)) := by
  have hτ : τ.toPointedCone = PointedCone.hull R ((i '' (S : Set M)) ∩ τ) :=
    τ.isFaceOf.eq_hull_inter_of_eq_hull rfl
  rw [hτ]
  congr 1
  ext v
  simp only [Set.mem_inter_iff, Set.mem_image, SetLike.mem_coe, Function.comp_apply,
    AddSubmonoid.coe_subtype]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨x, hxS, rfl⟩, hv⟩
    exact ⟨⟨x, hxS⟩, h ▸ (mem_hullFaceOrderEmbedding τ ⟨x, hxS⟩).2 hv, rfl⟩
  · rintro ⟨s, hsF, rfl⟩
    exact ⟨⟨s.val, s.property, rfl⟩, (mem_hullFaceOrderEmbedding τ s).1 (h.symm ▸ hsF)⟩

end OrderedSemiring

section Rational

variable {M V : Type*} [AddCommMonoid M] [AddCommGroup V] [Module ℚ V]

private theorem mem_hull_rat_image_saturated_iff (C : PointedCone ℚ V)
    (F : SaturatedAddSubmonoid C) (x : C) :
    (x : V) ∈ PointedCone.hull ℚ (C.toAddSubmonoid.subtype '' (F : Set C)) ↔ x ∈ F := by
  have hmem := mem_hull_rat_image_iff_mem_nsmulSaturation (S := F.toAddSubmonoid)
    C.toAddSubmonoid.subtype_injective (x := x)
  rw [AddSubmonoid.nsmulSaturation_eq_self F.nsmulSaturated] at hmem
  rw [AddSubmonoid.coe_subtype] at hmem
  exact hmem

/-- Every saturated additive submonoid `F` of a rational pointed cone `C : PointedCone ℚ V` spans a
face of `C`. -/
theorem isFaceOf_hull_rat_of_saturatedAddSubmonoid (C : PointedCone ℚ V)
    (F : SaturatedAddSubmonoid C) :
    (PointedCone.hull ℚ (C.toAddSubmonoid.subtype '' (F : Set C))).IsFaceOf C := by
  have hle : PointedCone.hull ℚ (C.toAddSubmonoid.subtype '' (F : Set C)) ≤ C := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, -, rfl⟩
    exact x.property
  refine ⟨hle, fun {x y a} hx hy ha hxy ↦ (mem_hull_rat_image_saturated_iff C F ⟨x, hx⟩).2 ?_⟩
  let q : ℕ := a.den
  let p : ℕ := a.num.toNat
  have hp_pos : 0 < p := Int.lt_toNat.2 (Rat.num_pos.2 ha)
  have hp_cast : (p : ℚ) = a.num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 ha.le)
  have hqa : (q : ℚ) * a = p := by
    rw [mul_comm, hp_cast]
    exact a.mul_den_eq_num
  have hq_mem : p • x + q • y ∈
      PointedCone.hull ℚ (C.toAddSubmonoid.subtype '' (F : Set C)) := by
    have hsmul := Submodule.smul_mem
      (PointedCone.hull ℚ (C.toAddSubmonoid.subtype '' (F : Set C)))
      (⟨q, Nat.cast_nonneg q⟩ : {c : ℚ // 0 ≤ c}) hxy
    rw [← Nonneg.coe_smul, smul_add, smul_smul, hqa, Nat.cast_smul_eq_nsmul,
      Nat.cast_smul_eq_nsmul] at hsmul
    exact hsmul
  have hsumF : p • (⟨x, hx⟩ : C) + q • (⟨y, hy⟩ : C) ∈ F :=
    (mem_hull_rat_image_saturated_iff C F (p • ⟨x, hx⟩ + q • ⟨y, hy⟩)).1 hq_mem
  exact (F.nsmulSaturated ((F.addSaturated hsumF).1)).resolve_left hp_pos.ne'

/-- Over `ℚ`, the face lattice of any pointed cone `C` is canonically order-isomorphic to
`SaturatedAddSubmonoid C`. -/
def faceOrderIsoSaturatedAddSubmonoid (C : PointedCone ℚ V) :
    C.Face ≃o SaturatedAddSubmonoid C where
  toFun := C.faceOrderEmbeddingSaturatedAddSubmonoid
  invFun F :=
    ⟨PointedCone.hull ℚ (C.toAddSubmonoid.subtype '' (F : Set C)),
      isFaceOf_hull_rat_of_saturatedAddSubmonoid C F⟩
  left_inv τ := by
    apply C.faceOrderEmbeddingSaturatedAddSubmonoid.injective
    refine SetLike.ext fun x ↦ ?_
    rw [mem_faceOrderEmbeddingSaturatedAddSubmonoid]
    exact mem_hull_rat_image_saturated_iff C (C.faceOrderEmbeddingSaturatedAddSubmonoid τ) x
  right_inv F := by
    refine SetLike.ext fun x ↦ ?_
    rw [mem_faceOrderEmbeddingSaturatedAddSubmonoid]
    exact mem_hull_rat_image_saturated_iff C F x
  map_rel_iff' := C.faceOrderEmbeddingSaturatedAddSubmonoid.map_rel_iff

/-- Membership in `C.faceOrderIsoSaturatedAddSubmonoid τ` is membership of the underlying vector in
`τ`. -/
@[simp]
theorem mem_faceOrderIsoSaturatedAddSubmonoid {C : PointedCone ℚ V} (τ : C.Face) (x : C) :
    x ∈ C.faceOrderIsoSaturatedAddSubmonoid τ ↔ (x : V) ∈ τ := by
  simp [faceOrderIsoSaturatedAddSubmonoid]

/-- Along any injective additive homomorphism `i : M →+ V` into a `ℚ`-module, the faces of the
rational cone generated by `i '' S` correspond order-isomorphically to the faces of `S`, with no
finite-generation hypothesis on `S`. -/
def hullRatFaceOrderIso {i : M →+ V} (hi : Function.Injective i) (S : AddSubmonoid M) :
    (PointedCone.hull ℚ (i '' (S : Set M))).Face ≃o SaturatedAddSubmonoid S :=
  (PointedCone.hull ℚ (i '' (S : Set M))).faceOrderIsoSaturatedAddSubmonoid.trans
    (SaturatedAddSubmonoid.comapOrderIsoOfNSMulSaturation (toHull_injective ℚ hi S) fun y ↦ by
      have hy : y.val ∈ (AddSubmonoid.closure (i '' (S : Set M))).nsmulSaturation :=
        (mem_hull_rat_iff_mem_nsmulSaturation_closure (i '' (S : Set M))).1 y.property
      rw [← AddMonoidHom.map_mclosure, S.closure_eq] at hy
      obtain ⟨n, hn, hmap⟩ := AddSubmonoid.mem_nsmulSaturation.1 hy
      obtain ⟨s, hsS, his⟩ := AddSubmonoid.mem_map.1 hmap
      exact ⟨n, hn, ⟨s, hsS⟩, Subtype.ext his⟩)

/-- `hullRatFaceOrderIso` agrees with `hullFaceOrderEmbedding ℚ i S` on faces. -/
@[simp]
theorem hullRatFaceOrderIso_apply {i : M →+ V} (hi : Function.Injective i) (S : AddSubmonoid M)
    (τ : (PointedCone.hull ℚ (i '' (S : Set M))).Face) :
    hullRatFaceOrderIso hi S τ = hullFaceOrderEmbedding ℚ i S τ :=
  SetLike.ext fun _ ↦ by simp [hullRatFaceOrderIso]

/-- An element `s : S` belongs to `hullRatFaceOrderIso hi S τ` iff `i s ∈ τ`. -/
theorem mem_hullRatFaceOrderIso {i : M →+ V} (hi : Function.Injective i) (S : AddSubmonoid M)
    (τ : (PointedCone.hull ℚ (i '' (S : Set M))).Face) (s : S) :
    s ∈ hullRatFaceOrderIso hi S τ ↔ i s.val ∈ τ := by
  rw [hullRatFaceOrderIso_apply, mem_hullFaceOrderEmbedding]

/-- The inverse of `hullRatFaceOrderIso` sends a monoid face `F` to the rational cone generated by
the image of `F`. -/
@[simp]
theorem toPointedCone_hullRatFaceOrderIso_symm {i : M →+ V} (hi : Function.Injective i)
    (S : AddSubmonoid M) (F : SaturatedAddSubmonoid S) :
    ((hullRatFaceOrderIso hi S).symm F).toPointedCone =
      PointedCone.hull ℚ ((i ∘ S.subtype) '' (F : Set S)) :=
  toPointedCone_eq_hull_image_of_hullFaceOrderEmbedding_eq
    (by simpa only [← hullRatFaceOrderIso_apply hi] using
      (hullRatFaceOrderIso hi S).apply_symm_apply F)

end Rational

end PointedCone

namespace SaturatedAddSubmonoid

section IntegralExposure

variable {L : Type*} [AddCommGroup L] [Module.Free ℤ L]

/-- **Integral linear exposure of semigroup faces.** Every face `F` of a finitely generated
additive submonoid `S` of a free abelian group `L` is cut out inside `S` by an integral linear
functional `m : L →+ ℤ` that is nonnegative on `S`. -/
theorem exists_addMonoidHom_nonneg_and_eq_zero_iff {S : AddSubmonoid L} (hS : S.FG)
    (F : SaturatedAddSubmonoid S) :
    ∃ m : L →+ ℤ, (∀ s ∈ S, 0 ≤ m s) ∧ ∀ s : S, m s.val = 0 ↔ s ∈ F := by
  classical
  obtain ⟨t, ht⟩ := AddSubmonoid.isAddFG_iff.1 hS
  let gen : t → S := fun a ↦ ⟨a.val, ht ▸ AddSubmonoid.subset_closure a.property⟩
  obtain ⟨c, m, hsum, hm, hpos⟩ :=
    TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos
      (Sum.elim (fun a : t ↦ a.val) fun b : {a : t // gen a ∈ F} ↦ -(b.val.val : L))
  have hmS : ∀ y ∈ S, 0 ≤ m y := fun y hy ↦ by
    rw [← ht] at hy
    induction hy using AddSubmonoid.closure_induction with
    | mem z hz => exact hm (.inl ⟨z, hz⟩)
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [map_add]; exact add_nonneg ih₁ ih₂
  have hmF_gen (a : t) (haF : gen a ∈ F) : m a.val = 0 := by
    have h₁ : 0 ≤ m a.val := hm (.inl a)
    have h₂ : 0 ≤ -m a.val := by simpa using hm (.inr ⟨a, haF⟩)
    lia
  have hsumS : ∑ a : t, c (.inl a) • gen a =
      ∑ b : {a : t // gen a ∈ F}, c (.inr b) • gen b.val := Subtype.ext <| by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, smul_neg,
      Finset.sum_neg_distrib, add_neg_eq_zero] at hsum
    simpa [gen] using hsum
  have hpos_notMem (a : t) (ha : gen a ∉ F) : 0 < m a.val := by
    have hrhs : (∑ b : {a : t // gen a ∈ F}, c (.inr b) • gen b.val) ∈ F :=
      sum_mem fun b _ ↦ nsmul_mem b.property _
    rw [← hsumS, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)] at hrhs
    simpa [(F.nsmulSaturated (F.addSaturated hrhs).1).resolve_right ha] using hpos (.inl a)
  refine ⟨m, hmS, fun ⟨y, hyS⟩ ↦ ?_⟩
  have hs : y ∈ AddSubmonoid.closure (t : Set L) := ht.symm ▸ hyS
  induction hs using AddSubmonoid.closure_induction with
  | mem z hz =>
    exact ⟨fun hz0 ↦ by_contra fun hnot ↦ (hpos_notMem ⟨z, hz⟩ hnot).ne' hz0, hmF_gen ⟨z, hz⟩⟩
  | zero => exact ⟨fun _ ↦ zero_mem F, fun _ ↦ map_zero m⟩
  | add x w hx hw ihx ihw =>
    refine ⟨fun hxw ↦ ?_, fun hxwF ↦ ?_⟩
    · rw [map_add] at hxw
      obtain ⟨hx0, hw0⟩ := (add_eq_zero_iff_of_nonneg (hmS x (ht ▸ hx)) (hmS w (ht ▸ hw))).1 hxw
      exact add_mem ((ihx (ht ▸ hx)).1 hx0) ((ihw (ht ▸ hw)).1 hw0)
    · obtain ⟨hxF, hwF⟩ := F.addSaturated (x := ⟨x, ht ▸ hx⟩) (y := ⟨w, ht ▸ hw⟩) hxwF
      rw [map_add, (ihx (ht ▸ hx)).2 hxF, (ihw (ht ▸ hw)).2 hwF, add_zero]

/-- In any torsion-free abelian group `G`, every face `F` of a finitely generated submonoid `S` is
cut out inside `S` by an integral linear functional on `AddSubgroup.closure (S : Set G)`. -/
theorem exists_addMonoidHom_closure_nonneg_and_eq_zero_iff {G : Type*} [AddCommGroup G]
    [HasUniqueDiv G] {S : AddSubmonoid G} (hS : S.FG) (F : SaturatedAddSubmonoid S) :
    ∃ m : AddSubgroup.closure (S : Set G) →+ ℤ,
      (∀ s : S, 0 ≤ m (S.toGroupClosure s)) ∧ ∀ s : S, m (S.toGroupClosure s) = 0 ↔ s ∈ F := by
  have := hS.addSubgroupClosure
  let F' : SaturatedAddSubmonoid (S.comap (AddSubgroup.closure (S : Set G)).subtype) :=
    F.comap S.toGroupClosureEquiv.symm.toAddMonoidHom
  obtain ⟨m, hm, hm0⟩ := exists_addMonoidHom_nonneg_and_eq_zero_iff hS.comap_subtype_closure F'
  refine ⟨m, fun s ↦ hm (S.toGroupClosure s) ?_,
    fun s ↦ by simpa [F', SaturatedAddSubmonoid.mem_comap] using hm0 (S.toGroupClosureEquiv s)⟩
  rw [AddSubmonoid.mem_comap, AddSubgroup.coe_subtype, S.coe_toGroupClosure]; exact s.property

end IntegralExposure

end SaturatedAddSubmonoid

namespace PointedCone

section LinearOrderedRing

variable {R L V : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup L] [Module.Free ℤ L] [AddCommGroup V] [Module R V]

/-- For a finitely generated submonoid `S` of a free abelian group `L`, if every integral linear
functional `L →+ ℤ` extends along `i : L →+ V` to `Module.Dual R V`, then the faces of
`PointedCone.hull R (i '' S)` correspond order-isomorphically to the faces of `S`. -/
noncomputable def hullFaceOrderIsoOfDualExt {i : L →+ V}
    (hext : ∀ m : L →+ ℤ, ∃ φ : Module.Dual R V, ∀ x : L, φ (i x) = m x)
    {S : AddSubmonoid L} (hS : S.FG) :
    (PointedCone.hull R (i '' (S : Set L))).Face ≃o SaturatedAddSubmonoid S :=
  OrderIso.ofSurjective (hullFaceOrderEmbedding R i S) fun F ↦ by
    obtain ⟨m, hmS, hmF⟩ := F.exists_addMonoidHom_nonneg_and_eq_zero_iff hS
    obtain ⟨φ, hφ⟩ := hext m
    have hφC : ∀ v ∈ PointedCone.hull R (i '' (S : Set L)), 0 ≤ φ v := fun v hv ↦ by
      induction hv using Submodule.span_induction with
      | mem v hv => obtain ⟨x, hxS, rfl⟩ := hv; rw [hφ]; exact_mod_cast hmS x hxS
      | zero => simp
      | add _ _ _ _ ih₁ ih₂ => rw [map_add]; exact add_nonneg ih₁ ih₂
      | smul c _ _ ih =>
        rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]; exact mul_nonneg c.property ih
    refine ⟨⟨_, isFaceOf_inf_ker hφC⟩, SetLike.ext fun s ↦ ?_⟩
    simp only [mem_hullFaceOrderEmbedding, ← Face.mem_toPointedCone, Face.toPointedCone,
      Submodule.mem_inf, mem_ofSubmodule_iff, LinearMap.mem_ker, hφ, Int.cast_eq_zero, hmF]
    exact ⟨fun h ↦ h.2, fun hsF ↦ ⟨PointedCone.subset_hull ⟨s.val, s.property, rfl⟩, hsF⟩⟩

/-- `hullFaceOrderIsoOfDualExt` agrees with `hullFaceOrderEmbedding R i S`. -/
@[simp]
theorem hullFaceOrderIsoOfDualExt_apply {i : L →+ V}
    (hext : ∀ m : L →+ ℤ, ∃ φ : Module.Dual R V, ∀ x : L, φ (i x) = m x)
    {S : AddSubmonoid L} (hS : S.FG) (τ : (PointedCone.hull R (i '' (S : Set L))).Face) :
    hullFaceOrderIsoOfDualExt hext hS τ = hullFaceOrderEmbedding R i S τ := (rfl)

/-- The inverse of `hullFaceOrderIsoOfDualExt` sends a monoid face `F` to the cone generated by
the image of `F`. -/
@[simp]
theorem toPointedCone_hullFaceOrderIsoOfDualExt_symm {i : L →+ V}
    (hext : ∀ m : L →+ ℤ, ∃ φ : Module.Dual R V, ∀ x : L, φ (i x) = m x)
    {S : AddSubmonoid L} (hS : S.FG) (F : SaturatedAddSubmonoid S) :
    ((hullFaceOrderIsoOfDualExt hext hS).symm F).toPointedCone =
      PointedCone.hull R ((i ∘ S.subtype) '' (F : Set S)) :=
  toPointedCone_eq_hull_image_of_hullFaceOrderEmbedding_eq
    (by simpa only [← hullFaceOrderIsoOfDualExt_apply hext hS] using
      (hullFaceOrderIsoOfDualExt hext hS).apply_symm_apply F)

/-- Over any strictly ordered commutative ring `R` (such as `ℝ`, `ℚ`, or `ℤ`), the faces of the
cone generated by a finitely generated submonoid `S` of a free abelian group `L` in `R ⊗[ℤ] L`
correspond order-isomorphically to the faces of `S`. -/
noncomputable def hullBaseChangeFaceOrderIso (R : Type*) [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {S : AddSubmonoid L} (hS : S.FG) :
    (PointedCone.hull R (TensorProduct.mk ℤ R L 1 '' (S : Set L))).Face ≃o
      SaturatedAddSubmonoid S :=
  hullFaceOrderIsoOfDualExt (i := (TensorProduct.mk ℤ R L 1).toAddMonoidHom)
    (fun m ↦ ⟨(((Int.castAddHom R).comp m).toIntLinearMap).liftBaseChange R,
      fun x ↦ by simp⟩)
    hS

/-- `hullBaseChangeFaceOrderIso` agrees with `hullFaceOrderEmbedding` along `1 ⊗ ·`. -/
@[simp]
theorem hullBaseChangeFaceOrderIso_apply (R : Type*) [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {S : AddSubmonoid L} (hS : S.FG)
    (τ : (PointedCone.hull R (TensorProduct.mk ℤ R L 1 '' (S : Set L))).Face) :
    hullBaseChangeFaceOrderIso R hS τ =
      hullFaceOrderEmbedding R (TensorProduct.mk ℤ R L 1).toAddMonoidHom S τ :=
  (rfl)

/-- The inverse of `hullBaseChangeFaceOrderIso` sends a monoid face `F` to the cone generated by
the image of `F` in `R ⊗[ℤ] L`. -/
@[simp]
theorem toPointedCone_hullBaseChangeFaceOrderIso_symm (R : Type*) [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {S : AddSubmonoid L} (hS : S.FG) (F : SaturatedAddSubmonoid S) :
    ((hullBaseChangeFaceOrderIso R hS).symm F).toPointedCone =
      PointedCone.hull R (((TensorProduct.mk ℤ R L 1).toAddMonoidHom ∘ S.subtype) '' (F : Set S)) :=
  toPointedCone_hullFaceOrderIsoOfDualExt_symm _ hS F

end LinearOrderedRing

end PointedCone
