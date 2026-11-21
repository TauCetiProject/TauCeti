/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.MappingPath.Fiber

/-!
# Lifts to a mapping-path fibre and specified nullhomotopies

A strict lift of `c : C(X, B)` to `MappingPathFiber f k` is equivalent, as data, to a
nullhomotopy of `f.comp c` ending at the constant map with value `k`. This is the universal
property of the mapping-path fibre, with no compactness or CW hypotheses on `X`.

The correspondence commutes with precomposition. It also identifies homotopies of lifts
over the fixed map `c` with homotopies of nullhomotopies relative to their two ends.
Thus one may use nullhomotopies to study lifts without forgetting either the chosen
nullhomotopy or the requirement that homotopies lie over the classifier.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.7.
-/

public section

open unitInterval

namespace TauCeti.MappingPathFiber

variable {X Y B K : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace B] [TopologicalSpace K]
  (f : C(B, K)) (k : K) (c : C(X, B))

/-- A specified nullhomotopy constructs a strict lift to the mapping-path fibre. -/
def liftOfHomotopy (H : (f.comp c).Homotopy (.const X k)) :
    C(X, MappingPathFiber f k) where
  toFun x := ⟨(c x, (H.toContinuousMap.comp .prodSwap).curry x),
    H.apply_zero x, H.apply_one x⟩
  continuous_toFun := (c.continuous.prodMk
    (H.toContinuousMap.comp .prodSwap).curry.continuous).subtype_mk _

@[simp]
theorem liftOfHomotopy_val (H : (f.comp c).Homotopy (.const X k)) (x : X) :
    (liftOfHomotopy f k c H x).val =
      (c x, (H.toContinuousMap.comp .prodSwap).curry x) := (rfl)

/-- The lift constructed from a nullhomotopy projects to the classifier `c`. -/
@[simp]
theorem proj_comp_liftOfHomotopy (H : (f.comp c).Homotopy (.const X k)) :
    (proj f k).comp (liftOfHomotopy f k c H) = c := by
  ext x
  simp [liftOfHomotopy]

/-- Read a specified nullhomotopy from a strict lift to the mapping-path fibre. -/
def homotopyOfLift (l : C(X, MappingPathFiber f k)) (hl : (proj f k).comp l = c) :
    (f.comp c).Homotopy (.const X k) where
  toFun z := (l z.2).val.2 z.1
  continuous_toFun := (continuous_subtype_val.snd.comp
    (l.continuous.comp continuous_snd)).eval continuous_fst
  map_zero_left x := (l x).property.1.trans
    (congrArg f (by simpa using ContinuousMap.congr_fun hl x))
  map_one_left x := (l x).property.2

@[simp]
theorem homotopyOfLift_apply (l : C(X, MappingPathFiber f k))
    (hl : (proj f k).comp l = c) (t : I) (x : X) :
    homotopyOfLift f k c l hl (t, x) = (l x).val.2 t := (rfl)

/-- Strict lifts over `c` are equivalent to specified nullhomotopies of `f.comp c`.
The homotopy parameter increases from `f.comp c` to the constant map at `k`. -/
def liftEquivHomotopy :
    {l : C(X, MappingPathFiber f k) // (proj f k).comp l = c} ≃
      (f.comp c).Homotopy (.const X k) where
  toFun l := homotopyOfLift f k c l.val l.property
  invFun H := ⟨liftOfHomotopy f k c H, proj_comp_liftOfHomotopy f k c H⟩
  left_inv l := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact Prod.ext (by simpa using (ContinuousMap.congr_fun l.property x).symm) rfl
  right_inv H := by
    apply ContinuousMap.Homotopy.ext
    rintro ⟨t, x⟩
    -- Reading the path at `x` and evaluating at `t` reverses the swap and currying.
    rw [homotopyOfLift_apply, liftOfHomotopy_val]
    simp only [ContinuousMap.curry_apply, ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply]
    rfl -- Evaluating `H.toContinuousMap` is evaluating `H`.

@[simp]
theorem liftEquivHomotopy_apply (l : C(X, MappingPathFiber f k))
    (hl : (proj f k).comp l = c) :
    liftEquivHomotopy f k c ⟨l, hl⟩ = homotopyOfLift f k c l hl := (rfl)

@[simp]
theorem liftEquivHomotopy_symm_val (H : (f.comp c).Homotopy (.const X k)) :
    ((liftEquivHomotopy f k c).symm H).val = liftOfHomotopy f k c H := (rfl)

/-- Constructing a strict lift from a nullhomotopy commutes with precomposition. -/
@[simp]
theorem liftOfHomotopy_comp (H : (f.comp c).Homotopy (.const X k)) (a : C(Y, X)) :
    liftOfHomotopy f k (c.comp a) (H.compContinuousMap a) =
      (liftOfHomotopy f k c H).comp a := (rfl)

/-- Reading a nullhomotopy from a strict lift commutes with precomposition. -/
@[simp]
theorem homotopyOfLift_comp (l : C(X, MappingPathFiber f k))
    (hl : (proj f k).comp l = c) (a : C(Y, X)) :
    homotopyOfLift f k (c.comp a) (l.comp a) (by rw [← ContinuousMap.comp_assoc, hl]) =
      ((homotopyOfLift f k c l hl).compContinuousMap a).cast
        (ContinuousMap.comp_assoc f c a) (ContinuousMap.const_comp k a) := (rfl)

/-- The lift–nullhomotopy equivalence commutes with source precomposition. -/
theorem liftEquivHomotopy_comp (a : C(Y, X)) :
    (liftEquivHomotopy f k (c.comp a)) ∘
        (fun l : {l : C(X, MappingPathFiber f k) // (proj f k).comp l = c} ↦
          ⟨l.val.comp a, by rw [← ContinuousMap.comp_assoc, l.property]⟩) =
      (fun H ↦ (H.compContinuousMap a).cast (ContinuousMap.comp_assoc f c a)
        (ContinuousMap.const_comp k a)) ∘ (liftEquivHomotopy f k c) := by
  funext l
  rcases l with ⟨l, hl⟩
  exact homotopyOfLift_comp f k c l hl a

/-- A strict lift exists exactly when the composite is nullhomotopic. This asserts existence,
not a replacement of the type of lifts by a proposition. -/
theorem exists_lift_iff_homotopic :
    (∃ l : C(X, MappingPathFiber f k), (proj f k).comp l = c) ↔
      (f.comp c).Homotopic (.const X k) := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨homotopyOfLift f k c l hl⟩
  · rintro ⟨H⟩
    exact ⟨liftOfHomotopy f k c H, proj_comp_liftOfHomotopy f k c H⟩

section Homotopies

variable (l₀ l₁ : C(X, MappingPathFiber f k))
  (h₀ : (proj f k).comp l₀ = c) (h₁ : (proj f k).comp l₁ = c)

private def homotopyRelOfHomotopyOver
    (F : ContinuousMap.HomotopyWith l₀ l₁ (fun l => (proj f k).comp l = c)) :
    ContinuousMap.HomotopyRel
      (homotopyOfLift f k c l₀ h₀).toContinuousMap
      (homotopyOfLift f k c l₁ h₁).toContinuousMap ({0, 1} ×ˢ Set.univ) where
  toFun z := (F (z.1, z.2.2)).val.2 z.2.1
  continuous_toFun := (continuous_subtype_val.snd.comp
    (F.continuous.comp (continuous_fst.prodMk continuous_snd.snd))).eval continuous_snd.fst
  map_zero_left := by rintro ⟨t, x⟩; simp
  map_one_left := by rintro ⟨t, x⟩; simp
  prop' s z hz := by
    rcases z with ⟨t, x⟩
    rcases hz.1 with ht | ht
    · have ht' : t = 0 := ht
      subst t
      have hc : (F (s, x)).val.1 = c x := by
        simpa using ContinuousMap.congr_fun (F.prop s) x
      exact ((F (s, x)).property.1.trans (congrArg f hc)).trans
        ((homotopyOfLift f k c l₀ h₀).apply_zero x).symm
    · have ht' : t = 1 := ht
      subst t
      exact (F (s, x)).property.2.trans
        ((homotopyOfLift f k c l₀ h₀).apply_one x).symm

private theorem homotopyRelOfHomotopyOver_apply
    (F : ContinuousMap.HomotopyWith l₀ l₁ (fun l => (proj f k).comp l = c))
    (s t : I) (x : X) :
    homotopyRelOfHomotopyOver f k c l₀ l₁ h₀ h₁ F (s, (t, x)) = (F (s, x)).val.2 t :=
  rfl

private def homotopyOverOfHomotopyRel
    (G : ContinuousMap.HomotopyRel
      (homotopyOfLift f k c l₀ h₀).toContinuousMap
      (homotopyOfLift f k c l₁ h₁).toContinuousMap ({0, 1} ×ˢ Set.univ)) :
    ContinuousMap.HomotopyWith l₀ l₁ (fun l => (proj f k).comp l = c) := by
  let N : (f.comp (c.comp .snd)).Homotopy (.const (I × X) k) := {
    toFun z := G (z.2.1, (z.1, z.2.2))
    continuous_toFun := G.continuous.comp
      (continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd))
    map_zero_left z := by
      rw [G.eq_fst z.1 (by simp)]
      exact (homotopyOfLift f k c l₀ h₀).apply_zero z.2
    map_one_left z := by
      rw [G.eq_fst z.1 (by simp)]
      exact (homotopyOfLift f k c l₀ h₀).apply_one z.2 }
  refine {
    toContinuousMap := liftOfHomotopy f k (c.comp .snd) N
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }
  · intro x
    apply Subtype.ext
    refine Prod.ext (by simpa using (ContinuousMap.congr_fun h₀ x).symm) ?_
    exact ContinuousMap.ext fun t => G.apply_zero (t, x)
  · intro x
    apply Subtype.ext
    refine Prod.ext (by simpa using (ContinuousMap.congr_fun h₁ x).symm) ?_
    exact ContinuousMap.ext fun t => G.apply_one (t, x)
  · intro s
    ext x
    simp [liftOfHomotopy]

private theorem homotopyOverOfHomotopyRel_apply_snd
    (G : ContinuousMap.HomotopyRel
      (homotopyOfLift f k c l₀ h₀).toContinuousMap
      (homotopyOfLift f k c l₁ h₁).toContinuousMap ({0, 1} ×ˢ Set.univ))
    (s t : I) (x : X) :
    (homotopyOverOfHomotopyRel f k c l₀ l₁ h₀ h₁ G (s, x)).val.2 t = G (s, (t, x)) :=
  rfl

/-- Homotopies of lifts over the fixed classifier correspond to homotopies of their
nullhomotopies relative to both ends of the nullhomotopy parameter. -/
def homotopyOverEquivHomotopyRel :
    ContinuousMap.HomotopyWith l₀ l₁ (fun l => (proj f k).comp l = c) ≃
      ContinuousMap.HomotopyRel
        (homotopyOfLift f k c l₀ h₀).toContinuousMap
        (homotopyOfLift f k c l₁ h₁).toContinuousMap ({0, 1} ×ˢ Set.univ) where
  toFun := homotopyRelOfHomotopyOver f k c l₀ l₁ h₀ h₁
  invFun := homotopyOverOfHomotopyRel f k c l₀ l₁ h₀ h₁
  left_inv F := by
    apply ContinuousMap.HomotopyWith.ext
    intro z
    apply Subtype.ext
    apply Prod.ext
    · -- The inverse construction uses the fixed classifier as its first coordinate.
      trans c z.2
      · rfl
      · simpa using (ContinuousMap.congr_fun (F.prop z.1) z.2).symm
    · rfl
  right_inv G := by
    apply ContinuousMap.HomotopyWith.ext
    rintro ⟨s, t, x⟩
    -- Recover the original value by evaluating the lifted path at `t`.
    rw [homotopyRelOfHomotopyOver_apply, homotopyOverOfHomotopyRel_apply_snd]

@[simp]
theorem homotopyOverEquivHomotopyRel_apply
    (F : ContinuousMap.HomotopyWith l₀ l₁ (fun l => (proj f k).comp l = c))
    (s t : I) (x : X) :
    homotopyOverEquivHomotopyRel f k c l₀ l₁ h₀ h₁ F (s, (t, x)) =
      (F (s, x)).val.2 t := homotopyRelOfHomotopyOver_apply f k c l₀ l₁ h₀ h₁ F s t x

@[simp]
theorem homotopyOverEquivHomotopyRel_symm_apply_val
    (G : ContinuousMap.HomotopyRel
      (homotopyOfLift f k c l₀ h₀).toContinuousMap
      (homotopyOfLift f k c l₁ h₁).toContinuousMap ({0, 1} ×ˢ Set.univ))
    (s : I) (x : X) :
    ((homotopyOverEquivHomotopyRel f k c l₀ l₁ h₀ h₁).symm G (s, x)).val =
      (c x, (⟨fun t => G (s, (t, x)), G.continuous.comp (by fun_prop)⟩ : C(I, K))) := (rfl)

/-- Under the lift/nullhomotopy correspondence, homotopy over the classifier is precisely
homotopy relative to the ends of the nullhomotopy. -/
theorem homotopicWith_iff_homotopicRel :
    ContinuousMap.HomotopicWith l₀ l₁ (fun l => (proj f k).comp l = c) ↔
      (homotopyOfLift f k c l₀ h₀).toContinuousMap.HomotopicRel
        (homotopyOfLift f k c l₁ h₁).toContinuousMap ({0, 1} ×ˢ Set.univ) :=
  (homotopyOverEquivHomotopyRel f k c l₀ l₁ h₀ h₁).nonempty_congr

end Homotopies

end TauCeti.MappingPathFiber
