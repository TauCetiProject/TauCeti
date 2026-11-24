/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Quotient coordinates from a complementary parametrization

If `A.coprod B` is invertible, every ambient vector has a unique decomposition
`A u + B w`. The second coordinate identifies the quotient by `range A` with the
fixed parameter space of `B`. In particular, when `A` varies and `B` stays fixed,
the quotient coordinates are read off from the inverse of a family of operators
between fixed spaces. Ambient maps carrying one range into another induce coordinate
changes satisfying the cocycle law; ambient equivalences preserving the ranges give
invertible changes. This is useful for local coordinates on normal bundles.

When `A = T.domRestrict V` and `B = W.subtypeL` for submodules `V ≤ E` and `W ≤ F`,
invertibility of the restricted coproduct `(T.domRestrict V).coprod W.subtypeL` implies that `V`
is disjoint from `ker T` (`ContinuousLinearMap.disjoint_ker_of_isInvertible_coprod_domRestrict`),
`T` restricts to a continuous linear equivalence `V ≃L[R] V.map T`
(`ContinuousLinearMap.domRestrictEquivMap`,
`ContinuousLinearMap.isInvertible_restrict_map_of_isInvertible_coprod_domRestrict`), the image
`V.map T` is closed whenever `W` is `T₁`
(`ContinuousLinearMap.isClosed_map_of_isInvertible_coprod_domRestrict`), and over a ring `V.map T`
and `W` are topological complements
(`ContinuousLinearMap.isTopCompl_map_of_isInvertible_coprod_domRestrict`).

The construction uses Mathlib's total continuous-linear inverse and continuous
quotient lift. No norm, completeness, or choice of an inner product is required. The
coordinates, coordinate changes, and restricted-coproduct equivalences only need a semiring;
the identification with the quotient and topological-complement statement need a ring.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
the normal-bundle construction preceding Theorem 6.24.
-/

public section

namespace ContinuousLinearMap

section Semiring

variable {R E F G : Type*} [Semiring R]
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace F] [AddCommMonoid F] [Module R F] [ContinuousAdd F]
  [TopologicalSpace G] [AddCommMonoid G] [Module R G]
  {A : E →L[R] F} {B : G →L[R] F}

/-- The complementary coordinate of an ambient vector in the decomposition `A u + B w`.
It is zero when the coproduct is not invertible. -/
noncomputable def quotientRangeCoordinate (A : E →L[R] F) (B : G →L[R] F) : F →L[R] G :=
  snd R E G ∘L (A.coprod B).inverse

/-- The coordinate operator is the second component of the inverse coproduct. -/
theorem quotientRangeCoordinate_def (A : E →L[R] F) (B : G →L[R] F) :
    A.quotientRangeCoordinate B = snd R E G ∘L (A.coprod B).inverse :=
  (rfl)

/-- Without an invertible coproduct, the complementary coordinate is zero. -/
@[simp] theorem quotientRangeCoordinate_of_not_isInvertible
    (h : ¬(A.coprod B).IsInvertible) : A.quotientRangeCoordinate B = 0 := by
  simp [quotientRangeCoordinate_def, h]

/-- Tangent representatives have zero complementary coordinate. Without an invertible
coproduct this holds because the coordinate is zero. -/
@[simp] theorem quotientRangeCoordinate_apply_left (u : E) :
    A.quotientRangeCoordinate B (A u) = 0 := by
  by_cases h : (A.coprod B).IsInvertible
  · simpa [quotientRangeCoordinate] using congrArg Prod.snd (h.inverse_apply_self (u, 0))
  · simp [quotientRangeCoordinate_of_not_isInvertible h]

/-- A vector parametrized by the complement has its original complementary coordinate. -/
@[simp] theorem quotientRangeCoordinate_apply_right (h : (A.coprod B).IsInvertible) (w : G) :
    A.quotientRangeCoordinate B (B w) = w := by
  simpa [quotientRangeCoordinate] using congrArg Prod.snd (h.inverse_apply_self (0, w))

/-- Every ambient vector is a range vector plus the complementary representative of its
coordinate. -/
theorem exists_apply_add_apply_quotientRangeCoordinate_eq (h : (A.coprod B).IsInvertible)
    (y : F) : ∃ u, A u + B (A.quotientRangeCoordinate B y) = y :=
  ⟨((A.coprod B).inverse y).1, by simpa [quotientRangeCoordinate] using h.self_apply_inverse y⟩

/-- The kernel of the complementary coordinate is exactly the range being quotiented out. -/
@[simp] theorem ker_quotientRangeCoordinate (h : (A.coprod B).IsInvertible) :
    (A.quotientRangeCoordinate B).ker = A.range := by
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨u, hu⟩ := exists_apply_add_apply_quotientRangeCoordinate_eq h y
    have hy0 : A.quotientRangeCoordinate B y = 0 := LinearMap.mem_ker.mp hy
    exact ⟨u, by simpa [hy0] using hu⟩
  · rintro y ⟨u, rfl⟩
    exact quotientRangeCoordinate_apply_left u

end Semiring

section Ring

variable {R E F G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] [ContinuousAdd F]
  [TopologicalSpace G] [AddCommGroup G] [Module R G]
  {A : E →L[R] F} {B : G →L[R] F}

/-- The complementary representative differs from the original vector by an element of
the range being quotiented out. -/
theorem sub_apply_quotientRangeCoordinate_mem_range (h : (A.coprod B).IsInvertible) (y : F) :
    y - B (A.quotientRangeCoordinate B y) ∈ A.range := by
  obtain ⟨u, hu⟩ := exists_apply_add_apply_quotientRangeCoordinate_eq h y
  exact ⟨u, eq_sub_of_add_eq hu⟩

/-- The quotient of the ambient space by `range A`, parametrized by a fixed complementary
map `B`. The forward map takes complementary coordinates and the inverse takes the class
of `B w`. -/
noncomputable def quotientRangeEquiv (A : E →L[R] F) (B : G →L[R] F)
    (h : (A.coprod B).IsInvertible) : (F ⧸ A.range) ≃L[R] G :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (A.range.liftQL (A.quotientRangeCoordinate B)
      (ker_quotientRangeCoordinate h).ge)
    (A.range.mkQL ∘L B)
    (ContinuousLinearMap.ext fun w => by simp [quotientRangeCoordinate_apply_right h])
    (ContinuousLinearMap.ext fun z => by
      obtain ⟨y, rfl⟩ := A.range.mkQ_surjective z
      simp only [comp_apply, Submodule.liftQL_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
        id_apply]
      exact ((Submodule.Quotient.eq _).mpr (sub_apply_quotientRangeCoordinate_mem_range h y)).symm)

/-- On an ambient representative, the quotient equivalence reads the second inverse
coordinate. -/
@[simp] theorem quotientRangeEquiv_apply_mk (h : (A.coprod B).IsInvertible) (y : F) :
    A.quotientRangeEquiv B h (Submodule.Quotient.mk y) = A.quotientRangeCoordinate B y :=
  (rfl)

/-- The inverse quotient equivalence takes the class of the fixed complementary map. -/
@[simp] theorem quotientRangeEquiv_symm_apply (h : (A.coprod B).IsInvertible) (w : G) :
    (A.quotientRangeEquiv B h).symm w = Submodule.Quotient.mk (B w) :=
  (rfl)

end Ring

section CoordinateChange

variable {R E F G G' E' F' E'' F'' G'' : Type*} [Semiring R]
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace F] [AddCommMonoid F] [Module R F] [ContinuousAdd F]
  [TopologicalSpace G] [AddCommMonoid G] [Module R G]
  [TopologicalSpace G'] [AddCommMonoid G'] [Module R G']
  [TopologicalSpace E'] [AddCommMonoid E'] [Module R E']
  [TopologicalSpace F'] [AddCommMonoid F'] [Module R F'] [ContinuousAdd F']
  [TopologicalSpace E''] [AddCommMonoid E''] [Module R E'']
  [TopologicalSpace F''] [AddCommMonoid F''] [Module R F''] [ContinuousAdd F'']
  [TopologicalSpace G''] [AddCommMonoid G''] [Module R G'']
  {A : E →L[R] F} {B : G →L[R] F} {C : G' →L[R] F}
  {A' : E' →L[R] F'} {B' : G' →L[R] F'}
  {A'' : E'' →L[R] F''} {B'' : G'' →L[R] F''}

/-- Replacing an ambient representative by its complementary representative does not
change its coordinates after an ambient map carrying the first tangent range into the second. -/
@[simp] theorem quotientRangeCoordinate_comp_of_map_range_le
    (hB : (A.coprod B).IsInvertible) (T : F →L[R] F')
    (hT : A.range.map T.toLinearMap ≤ A'.range) :
    (A'.quotientRangeCoordinate B' ∘L T ∘L B) ∘L A.quotientRangeCoordinate B =
      A'.quotientRangeCoordinate B' ∘L T := by
  by_cases hB' : (A'.coprod B').IsInvertible
  · ext y
    obtain ⟨u, hu⟩ := exists_apply_add_apply_quotientRangeCoordinate_eq hB y
    have hTu : A'.quotientRangeCoordinate B' (T (A u)) = 0 := LinearMap.mem_ker.mp <| by
      rw [ker_quotientRangeCoordinate hB']
      exact hT (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ u))
    simpa [hTu] using congrArg (A'.quotientRangeCoordinate B' ∘L T) hu
  · simp [quotientRangeCoordinate_of_not_isInvertible hB']

/-- Changing complementary representatives preserves all quotient coordinates.
This identifies the transition from the `B` coordinates to the `C` coordinates. -/
@[simp] theorem quotientRangeCoordinate_comp_quotientRangeCoordinate
    (hB : (A.coprod B).IsInvertible) :
    (A.quotientRangeCoordinate C ∘L B) ∘L A.quotientRangeCoordinate B =
      A.quotientRangeCoordinate C := by
  simpa using quotientRangeCoordinate_comp_of_map_range_le (B' := C) hB (.id R F) (by simp)

omit [ContinuousAdd F] in
/-- Complementary coordinate changes satisfy the cocycle law, including changes of
ambient coordinates. Range containment suffices; the ambient maps need not be invertible. -/
@[simp] theorem quotientRangeCoordinate_comp_cocycle
    (hB' : (A'.coprod B').IsInvertible) (T : F →L[R] F') (U : F' →L[R] F'')
    (hU : A'.range.map U.toLinearMap ≤ A''.range) :
    (A''.quotientRangeCoordinate B'' ∘L U ∘L B') ∘L
      (A'.quotientRangeCoordinate B' ∘L T ∘L B) =
        A''.quotientRangeCoordinate B'' ∘L (U ∘L T) ∘L B := by
  rw [← comp_assoc, quotientRangeCoordinate_comp_of_map_range_le hB' U hU]
  simp only [comp_assoc]

/-- An ambient equivalence carrying one tangent range onto another induces an invertible
change between any valid complementary coordinates. -/
theorem isInvertible_quotientRangeCoordinate_comp_of_map_range_eq
    (hB : (A.coprod B).IsInvertible) (hB' : (A'.coprod B').IsInvertible)
    (T : F ≃L[R] F') (hT : A.range.map T.toLinearMap = A'.range) :
    (A'.quotientRangeCoordinate B' ∘L T.toContinuousLinearMap ∘L B).IsInvertible := by
  have hT' : A'.range.map T.symm.toLinearMap = A.range :=
    (Submodule.map_symm_eq_iff T.toLinearEquiv).mpr hT
  refine .of_inverse
    (g := A.quotientRangeCoordinate B ∘L T.symm.toContinuousLinearMap ∘L B') ?_ ?_
  · rw [quotientRangeCoordinate_comp_cocycle hB T.symm.toContinuousLinearMap
      T.toContinuousLinearMap hT.le]
    ext w
    simp [quotientRangeCoordinate_apply_right hB']
  · rw [quotientRangeCoordinate_comp_cocycle hB' T.toContinuousLinearMap
      T.symm.toContinuousLinearMap hT'.le]
    ext w
    simp [quotientRangeCoordinate_apply_right hB]

/-- Transitions between two valid complementary parametrizations are invertible. -/
theorem isInvertible_quotientRangeCoordinate_comp
    (hB : (A.coprod B).IsInvertible) (hC : (A.coprod C).IsInvertible) :
    (A.quotientRangeCoordinate C ∘L B).IsInvertible := by
  simpa using isInvertible_quotientRangeCoordinate_comp_of_map_range_eq hB hC
    (.refl R F) (Submodule.map_id _)

end CoordinateChange

/-! ### Pointwise consequences of an invertible restricted coproduct -/

section RestrictedCoprod

variable {R E F : Type*} [Semiring R]
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace F] [AddCommMonoid F] [Module R F] [ContinuousAdd F]
  {T : E →L[R] F} {V : Submodule R E} {W : Submodule R F}

/-- If `(T.domRestrict V).coprod W.subtypeL` is invertible, then `V` is disjoint from `ker T`. -/
theorem disjoint_ker_of_isInvertible_coprod_domRestrict
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    Disjoint V T.ker := by
  rw [Submodule.disjoint_def]
  intro x hxV hxker
  exact congrArg (fun p : V × W ↦ (p.1 : E)) <|
    hinv.injective (a₁ := (⟨x, hxV⟩, 0)) (a₂ := (0, 0)) <| by
      simpa using LinearMap.mem_ker.mp hxker

/-- When `(T.domRestrict V).coprod W.subtypeL` is invertible, `T` restricts to a continuous linear
equivalence between `V` and its image `V.map (T : E →ₗ[R] F)`. -/
noncomputable def domRestrictEquivMap
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    V ≃L[R] V.map (T : E →ₗ[R] F) :=
  have hfst (v : V) : (((T.domRestrict V).coprod W.subtypeL).inverse (T v)).1 = v := by
    simpa using congrArg Prod.fst (hinv.inverse_apply_self (v, 0))
  ContinuousLinearEquiv.ofContinuousLinearMap
    (T.restrict fun _ hx ↦ Submodule.mem_map_of_mem hx)
    (fst R V W ∘L ((T.domRestrict V).coprod W.subtypeL).inverse ∘L
      (V.map (T : E →ₗ[R] F)).subtypeL)
    (ContinuousLinearMap.ext fun ⟨_, v, hv, rfl⟩ ↦ by
      apply Subtype.ext
      simp [hfst ⟨v, hv⟩])
    (ContinuousLinearMap.ext fun v ↦ by simp [hfst])

/-- The underlying continuous linear map of `domRestrictEquivMap` is the restriction of `T` to
`V` and its image `V.map (T : E →ₗ[R] F)`. -/
@[simp]
theorem toContinuousLinearMap_domRestrictEquivMap
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    (domRestrictEquivMap hinv : V →L[R] V.map (T : E →ₗ[R] F)) =
      T.restrict fun _ hx ↦ Submodule.mem_map_of_mem hx :=
  (rfl)

/-- Applying `domRestrictEquivMap` and coercing to the ambient space recovers `T`. -/
@[simp]
theorem coe_domRestrictEquivMap_apply
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) (v : V) :
    (domRestrictEquivMap hinv v : F) = T v := by
  rw [← ContinuousLinearEquiv.coe_coe, toContinuousLinearMap_domRestrictEquivMap,
    coe_restrict_apply]

/-- The inverse of `domRestrictEquivMap` reads the `V`-component of the inverse coproduct. -/
@[simp]
theorem domRestrictEquivMap_symm_apply
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) (y : V.map (T : E →ₗ[R] F)) :
    (domRestrictEquivMap hinv).symm y =
      (((T.domRestrict V).coprod W.subtypeL).inverse (y : F)).1 := by
  simp [domRestrictEquivMap]

/-- When `(T.domRestrict V).coprod W.subtypeL` is invertible, the restriction
`T.restrict : V →L[R] V.map (T : E →ₗ[R] F)` is invertible. -/
theorem isInvertible_restrict_map_of_isInvertible_coprod_domRestrict
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    (T.restrict (fun _ hx ↦ Submodule.mem_map_of_mem hx :
      Set.MapsTo T V (V.map (T : E →ₗ[R] F)))).IsInvertible :=
  ⟨domRestrictEquivMap hinv, toContinuousLinearMap_domRestrictEquivMap hinv⟩

/-- When `(T.domRestrict V).coprod W.subtypeL` is invertible and `W` is `T₁`, the image `T(V)` is
closed in `F`. -/
theorem isClosed_map_of_isInvertible_coprod_domRestrict [T1Space W]
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    IsClosed (V.map (T : E →ₗ[R] F) : Set F) := by
  have hker := ker_quotientRangeCoordinate hinv
  rw [toLinearMap_domRestrict, LinearMap.range_domRestrict] at hker
  rw [← hker]
  exact isClosed_singleton.preimage
    ((T.domRestrict V).quotientRangeCoordinate W.subtypeL).continuous

end RestrictedCoprod

section RestrictedCoprodRing

variable {R E F : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] [ContinuousAdd F]
  {T : E →L[R] F} {V : Submodule R E} {W : Submodule R F}

/-- When `(T.domRestrict V).coprod W.subtypeL` is invertible, `V.map (T : E →ₗ[R] F)` and `W` are
topological complements in `F`. -/
theorem isTopCompl_map_of_isInvertible_coprod_domRestrict
    (hinv : ((T.domRestrict V).coprod W.subtypeL).IsInvertible) :
    Submodule.IsTopCompl (V.map (T : E →ₗ[R] F)) W := by
  let p : F →L[R] V := fst R V W ∘L ((T.domRestrict V).coprod W.subtypeL).inverse
  have hp : Function.LeftInverse p (T.domRestrict V) := fun v ↦ by
    simpa [p] using congrArg Prod.fst (hinv.inverse_apply_self (v, 0))
  have hker : p.ker = W := by
    refine le_antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_)
    · have h1 : (((T.domRestrict V).coprod W.subtypeL).inverse y).1 = 0 :=
        LinearMap.mem_ker.mp hy
      have hself := hinv.self_apply_inverse y
      simp only [coprod_apply, h1, map_zero, zero_add, Submodule.coe_subtypeL,
        Submodule.coe_subtype] at hself
      exact hself ▸ (((T.domRestrict V).coprod W.subtypeL).inverse y).2.property
    · simpa [p] using congrArg Prod.fst (hinv.inverse_apply_self (0, ⟨y, hy⟩))
  simpa [toLinearMap_domRestrict, LinearMap.range_domRestrict, hker] using
    (T.domRestrict V).isTopCompl_range_ker_of_leftInverse p hp

end RestrictedCoprodRing

end ContinuousLinearMap
