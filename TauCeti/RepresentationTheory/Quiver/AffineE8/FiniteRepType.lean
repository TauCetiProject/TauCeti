/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AffineE8.Basic
public import TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType

/-!
# The extended Dynkin quiver `E₈~` has infinite representation type

A vector space `V` with an endomorphism `f` gives three flags in `V⁶`. The long arm is the
standard full flag, the medium arm is the flag on the last two and last four coordinates,
and the short arm is the image of
`(x,y,z) ↦ (x, x+z, y, x+f(y), z, y+z)`.

Preserving the first two flags forces a morphism to act by three upper triangular two-by-two
blocks. Preserving the short subspace kills the off-diagonal entries, equates the diagonal
maps and forces the common map to intertwine the endomorphisms. Thus the construction is
fully faithful, preserves finite-dimensionality and indecomposability, and reflects
isomorphisms. The loop quiver's nilpotent Jordan blocks give infinite representation type
over every field, including finite fields and fields of characteristic two.

The construction and API follow the analogous `E₆~` construction in
`TauCeti.RepresentationTheory.Quiver.AffineE6.FiniteRepType`. The coordinate calculation
uses no division.

## References

* Assem–Simson–Skowroński, *Elements of the Representation Theory of Associative Algebras* I,
  Chapter VII.
* Derksen–Weyman, *An Introduction to Quiver Representations*, Chapter 4.
-/

public section

namespace TauCeti

open CategoryTheory Quiver.AffineE8

universe u w t

section ArrowMaps

variable {k : Type u} [Semiring k]

/-- The maps of the three standard flags associated to an endomorphism: prefix inclusions on
the long arm, suffix inclusions on the medium arm, and the map involving `f` on the short arm. -/
def Quiver.AffineE8.arrowMap {V : Type t} [AddCommMonoid V] [Module k V]
    {a b : Quiver.AffineE8} (e : a ⟶ b) (f : V →ₗ[k] V) :
    (Fin (coordinateCount a) → V) →ₗ[k] (Fin (coordinateCount b) → V) :=
  match e with
  | .short =>
    let p (i : Fin 3) : (Fin 3 → V) →ₗ[k] V := LinearMap.proj i
    LinearMap.pi ![p 0, p 0 + p 2, p 1, p 0 + f.comp (p 1), p 2, p 1 + p 2]
  | .medium2 =>
    let p (i : Fin 2) : (Fin 2 → V) →ₗ[k] V := LinearMap.proj i
    LinearMap.pi ![0, 0, p 0, p 1]
  | .medium4 =>
    let p (i : Fin 4) : (Fin 4 → V) →ₗ[k] V := LinearMap.proj i
    LinearMap.pi ![0, 0, p 0, p 1, p 2, p 3]
  | .long1 =>
    let p (i : Fin 1) : (Fin 1 → V) →ₗ[k] V := LinearMap.proj i
    LinearMap.pi ![p 0, 0]
  | .long2 =>
    let p (i : Fin 2) : (Fin 2 → V) →ₗ[k] V := LinearMap.proj i
    LinearMap.pi ![p 0, p 1, 0]
  | .long3 =>
    let p (i : Fin 3) : (Fin 3 → V) →ₗ[k] V := LinearMap.proj i
    LinearMap.pi ![p 0, p 1, p 2, 0]
  | .long4 =>
    let p (i : Fin 4) : (Fin 4 → V) →ₗ[k] V := LinearMap.proj i
    LinearMap.pi ![p 0, p 1, p 2, p 3, 0]
  | .long5 =>
    let p (i : Fin 5) : (Fin 5 → V) →ₗ[k] V := LinearMap.proj i
    LinearMap.pi ![p 0, p 1, p 2, p 3, p 4, 0]

/-- The flag arrow maps, in coordinates. -/
@[simp] theorem Quiver.AffineE8.arrowMap_apply {V : Type t} [AddCommMonoid V] [Module k V]
    {a b : Quiver.AffineE8} (e : a ⟶ b) (f : V →ₗ[k] V)
    (x : Fin (coordinateCount a) → V) :
    arrowMap e f x = match e with
      | .short => ![x 0, x 0 + x 2, x 1,
          x 0 + f (x 1), x 2, x 1 + x 2]
      | .medium2 => ![0, 0, x 0, x 1]
      | .medium4 => ![0, 0, x 0, x 1, x 2, x 3]
      | .long1 => ![x 0, 0]
      | .long2 => ![x 0, x 1, 0]
      | .long3 => ![x 0, x 1, x 2, 0]
      | .long4 => ![x 0, x 1, x 2, x 3, 0]
      | .long5 => ![x 0, x 1, x 2, x 3, x 4, 0] := by
  cases e <;> funext i <;> fin_cases i <;> rfl

end ArrowMaps

variable {k : Type u} [Field k]

private abbrev LoopSpace (M : QuiverRep.{u, 0, w, t} k Quiver.OneLoop) :=
  M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)

/-- A loop representation as three flags in the sixth power of its vertex space.
The long arm is the standard full flag, the medium arm the last-two/last-four flag,
and the short arm is `(x,y,z) ↦ (x,x+z,y,x+f(y),z,y+z)`.
The body is exposed so that the vertex-space types can be used in the coordinate API. -/
@[expose] noncomputable def affineE8LoopRep
    (M : QuiverRep.{u, 0, w, t} k Quiver.OneLoop) :
    QuiverRep.{u, 0, 0, t} k Quiver.AffineE8 :=
  Paths.lift
    { obj v := ModuleCat.of k
        (Fin (coordinateCount v) → M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop))
      map e := ModuleCat.ofHom (arrowMap e (M.map Quiver.OneLoop.loop.toPath).hom) }

variable {M N : QuiverRep.{u, 0, w, t} k Quiver.OneLoop}

/-- The vertex spaces are powers of the loop vertex space, with the imaginary-root
multiplicities. -/
@[simp] theorem affineE8LoopRep_obj (v : Quiver.AffineE8) :
    (affineE8LoopRep M).obj (v : Paths Quiver.AffineE8) =
      ModuleCat.of k
        (Fin (coordinateCount v) → M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :=
  (rfl)

/-- The representation uses the standard flag map on each arrow. -/
@[simp] theorem affineE8LoopRep_map_arrow {a b : Quiver.AffineE8} (e : a ⟶ b) :
    (affineE8LoopRep M).map e.toPath =
      ModuleCat.ofHom (arrowMap e (M.map Quiver.OneLoop.loop.toPath).hom) :=
  Paths.lift_toPath _ _

/-- The path from a vertex to the centre along its arm. -/
private def toCenter : (v : Quiver.AffineE8) → _root_.Quiver.Path v center
  | center => .nil
  | short => (_root_.Quiver.Hom.toPath Arrow.short)
  | medium4 => (_root_.Quiver.Hom.toPath Arrow.medium4)
  | medium2 => (_root_.Quiver.Hom.toPath Arrow.medium2).comp (toCenter medium4)
  | long5 => (_root_.Quiver.Hom.toPath Arrow.long5)
  | long4 => (_root_.Quiver.Hom.toPath Arrow.long4).comp (toCenter long5)
  | long3 => (_root_.Quiver.Hom.toPath Arrow.long3).comp (toCenter long4)
  | long2 => (_root_.Quiver.Hom.toPath Arrow.long2).comp (toCenter long3)
  | long1 => (_root_.Quiver.Hom.toPath Arrow.long1).comp (toCenter long2)
termination_by v => 6 - coordinateCount v
decreasing_by all_goals decide

private def centerVector (M : QuiverRep.{u, 0, w, t} k Quiver.OneLoop) :
    (v : Quiver.AffineE8) → (Fin (coordinateCount v) → LoopSpace M) → (Fin 6 → LoopSpace M)
  | center, x => x
  | short, x => ![x 0, x 0 + x 2, x 1,
      x 0 + (M.map Quiver.OneLoop.loop.toPath).hom (x 1), x 2, x 1 + x 2]
  | medium2, x => ![0, 0, 0, 0, x 0, x 1]
  | medium4, x => ![0, 0, x 0, x 1, x 2, x 3]
  | long1, x => ![x 0, 0, 0, 0, 0, 0]
  | long2, x => ![x 0, x 1, 0, 0, 0, 0]
  | long3, x => ![x 0, x 1, x 2, 0, 0, 0]
  | long4, x => ![x 0, x 1, x 2, x 3, 0, 0]
  | long5, x => ![x 0, x 1, x 2, x 3, x 4, 0]

private theorem map_toCenter (v : Quiver.AffineE8) (x : Fin (coordinateCount v) → LoopSpace M) :
    ((affineE8LoopRep M).map (toCenter v)).hom x = centerVector M v x := by
  cases v <;> simp only [toCenter] <;> apply funext <;> intro i <;> fin_cases i <;> rfl

/-- A finite-dimensional loop representation gives finite-dimensional flag spaces. -/
theorem isFinDim_affineE8LoopRep (hM : IsFinDim k Quiver.OneLoop M) :
    IsFinDim k Quiver.AffineE8 (affineE8LoopRep M) := by
  have := isFinDim_iff.mp hM (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)
  exact isFinDim_iff.mpr fun v ↦
    inferInstanceAs (FiniteDimensional k (Fin (coordinateCount v) → LoopSpace M))

private noncomputable def loopApp (φ : M ⟶ N) (v : Quiver.AffineE8) :
    (affineE8LoopRep M).obj v ⟶ (affineE8LoopRep N).obj v :=
  ModuleCat.ofHom
    ((φ.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom.compLeft (Fin (coordinateCount v)))

private theorem arrowMap_naturality {V W : Type t}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] V) (f' : W →ₗ[k] W) (ψ : V →ₗ[k] W)
    (h : ∀ x, ψ (f x) = f' (ψ x)) {a b : Quiver.AffineE8} (e : a ⟶ b)
    (x : Fin (coordinateCount a) → V) :
    (fun i ↦ ψ (arrowMap e f x i)) = arrowMap e f' (fun i ↦ ψ (x i)) := by
  cases e <;> funext i <;> fin_cases i <;> simp [arrowMap, h]

private theorem loopApp_naturality (φ : M ⟶ N) {a b : Quiver.AffineE8} (e : a ⟶ b) :
    (affineE8LoopRep M).map e.toPath ≫ loopApp φ b =
      loopApp φ a ≫ (affineE8LoopRep N).map e.toPath := by
  -- Retype the components as linear maps on coordinate spaces: this avoids instance
  -- comparison through the object coercions of `Paths.lift`.
  exact ModuleCat.hom_ext (LinearMap.ext fun x ↦
    arrowMap_naturality (M.map Quiver.OneLoop.loop.toPath).hom
      (N.map Quiver.OneLoop.loop.toPath).hom
      (φ.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom
      (NatTrans.naturality_apply φ Quiver.OneLoop.loop.toPath) e x)

/-- A morphism of loop representations acts coordinatewise on every flag space. -/
noncomputable def affineE8LoopFunctor (k : Type u) [Field k] :
    QuiverRep.{u, 0, w, t} k Quiver.OneLoop ⥤ QuiverRep.{u, 0, 0, t} k Quiver.AffineE8 where
  obj M := affineE8LoopRep M
  map φ := Paths.liftNatTrans (loopApp φ) (loopApp_naturality φ)
  map_id M := by
    apply NatTrans.ext
    exact funext fun v ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ funext fun i ↦ rfl)
  map_comp φ ψ := by
    apply NatTrans.ext
    exact funext fun v ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ funext fun i ↦ rfl)

/-- The functor's object construction is the flag representation. -/
@[simp] theorem affineE8LoopFunctor_obj :
    (affineE8LoopFunctor k).obj M = affineE8LoopRep M := (rfl)

/-- The functor acts coordinatewise on morphisms, transported to its vertex spaces. -/
@[simp] theorem affineE8LoopFunctor_map_app (φ : M ⟶ N) (v : Quiver.AffineE8) :
    ((affineE8LoopFunctor k).map φ).app (v : Paths Quiver.AffineE8) =
      eqToHom (Functor.congr_obj (affineE8LoopFunctor_obj (M := M)) v) ≫
      ModuleCat.ofHom
        ((φ.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom.compLeft
          (Fin (coordinateCount v))) ≫
      eqToHom (Functor.congr_obj (affineE8LoopFunctor_obj (M := N)) v).symm := (rfl)

section Full

variable (g : affineE8LoopRep M ⟶ affineE8LoopRep N)

private noncomputable def component (v : Quiver.AffineE8) :
    (Fin (coordinateCount v) → LoopSpace M) →ₗ[k] (Fin (coordinateCount v) → LoopSpace N) :=
  (g.app (v : Paths Quiver.AffineE8)).hom

private theorem center_naturality (v : Quiver.AffineE8)
    (x : Fin (coordinateCount v) → LoopSpace M) :
    component g center (centerVector M v x) = centerVector N v (component g v x) := by
  have h : (g.app (center : Paths Quiver.AffineE8)).hom
        (((affineE8LoopRep M).map (toCenter v)).hom x) =
      ((affineE8LoopRep N).map (toCenter v)).hom
        ((g.app (v : Paths Quiver.AffineE8)).hom x) :=
    NatTrans.naturality_apply g (toCenter v) x
  erw [map_toCenter (M := M) v x, map_toCenter (M := N) v (component g v x)] at h
  exact h

private noncomputable def entry (i j : Fin 6) : LoopSpace M →ₗ[k] LoopSpace N :=
  (LinearMap.proj i).comp ((component g center).comp (LinearMap.single k _ j))

private theorem entry_apply (i j : Fin 6) (x : LoopSpace M) :
    entry g i j x = component g center (Pi.single j x) i := (rfl)

private theorem center_single {v : Quiver.AffineE8} {j : Fin 6} (x : LoopSpace M)
    (y : Fin (coordinateCount v) → LoopSpace M) (hy : centerVector M v y = Pi.single j x) :
    component g center (Pi.single j x) = centerVector N v (component g v y) :=
  (congrArg (component g center) hy).symm.trans (center_naturality g v y)

private theorem entry_zero (i j : Fin 6) (hij : j.val < i.val ∨ i.val / 2 ≠ j.val / 2)
    (x : LoopSpace M) : entry g i j x = 0 := by
  -- The long flag gives the lower zeros; the last-two/last-four flag gives the zeros
  -- above the three diagonal blocks. Test naturality on the corresponding coordinate axes.
  have h0 := center_single g (v := long1) (j := 0) x (Pi.single 0 x) (by
    funext l
    fin_cases l <;> simp [centerVector, Fin.ext_iff, coordinateCount])
  have h1 := center_single g (v := long2) (j := 1) x (Pi.single 1 x) (by
    funext l
    fin_cases l <;> simp [centerVector, Fin.ext_iff, coordinateCount])
  have h2 := center_single g (v := long3) (j := 2) x (Pi.single 2 x) (by
    funext l
    fin_cases l <;> simp [centerVector, Fin.ext_iff, coordinateCount])
  have h3 := center_single g (v := long4) (j := 3) x (Pi.single 3 x) (by
    funext l
    fin_cases l <;> simp [centerVector, Fin.ext_iff, coordinateCount])
  have h4 := center_single g (v := long5) (j := 4) x (Pi.single 4 x) (by
    funext l
    fin_cases l <;> simp [centerVector, Fin.ext_iff, coordinateCount])
  have h2m := center_single g (v := medium4) (j := 2) x (Pi.single 0 x) (by
    funext l
    fin_cases l <;> simp [centerVector, Fin.ext_iff, coordinateCount])
  have h3m := center_single g (v := medium4) (j := 3) x (Pi.single 1 x) (by
    funext l
    fin_cases l <;> simp [centerVector, Fin.ext_iff, coordinateCount])
  have h4m := center_single g (v := medium2) (j := 4) x (Pi.single 0 x) (by
    funext l
    fin_cases l <;> simp [centerVector, Fin.ext_iff, coordinateCount])
  have h5m := center_single g (v := medium2) (j := 5) x (Pi.single 1 x) (by
    funext l
    fin_cases l <;> simp [centerVector, Fin.ext_iff, coordinateCount])
  rw [entry_apply]
  fin_cases j <;> fin_cases i <;> norm_num [coordinateCount] at hij
  all_goals first
    | (solve | apply (congrFun h0 _).trans; simp [centerVector, coordinateCount])
    | (solve | apply (congrFun h1 _).trans; simp [centerVector, coordinateCount])
    | (solve | apply (congrFun h2 _).trans; simp [centerVector, coordinateCount])
    | (solve | apply (congrFun h3 _).trans; simp [centerVector, coordinateCount])
    | (solve | apply (congrFun h4 _).trans; simp [centerVector, coordinateCount])
    | (solve | apply (congrFun h2m _).trans; simp [centerVector, coordinateCount])
    | (solve | apply (congrFun h3m _).trans; simp [centerVector, coordinateCount])
    | (solve | apply (congrFun h4m _).trans; simp [centerVector, coordinateCount])
    | (solve | apply (congrFun h5m _).trans; simp [centerVector, coordinateCount])

private theorem center_apply (x : Fin 6 → LoopSpace M) :
    component g center x =
      ![entry g 0 0 (x 0) + entry g 0 1 (x 1), entry g 1 1 (x 1),
        entry g 2 2 (x 2) + entry g 2 3 (x 3), entry g 3 3 (x 3),
        entry g 4 4 (x 4) + entry g 4 5 (x 5), entry g 5 5 (x 5)] := by
  have hx : component g center x = ∑ j : Fin 6, fun i ↦ entry g i j (x j) := by
    -- Retype the coordinate projections before summing, to avoid object-coercion instances.
    calc
      component g center x = ∑ j : Fin 6, component g center (Pi.single j (x j)) := by
        rw [← map_sum, LinearMap.sum_single_apply]
      _ = _ := by rfl
  rw [hx]
  funext i
  fin_cases i <;> simp [Fin.sum_univ_succ, entry_zero]

private theorem short_relation (x y z : LoopSpace M) :
    ![entry g 0 0 x + entry g 0 1 (x + z), entry g 1 1 (x + z),
      entry g 2 2 y + entry g 2 3 (x + (M.map Quiver.OneLoop.loop.toPath).hom y),
      entry g 3 3 (x + (M.map Quiver.OneLoop.loop.toPath).hom y),
      entry g 4 4 z + entry g 4 5 (y + z), entry g 5 5 (y + z)] =
      centerVector N short (component g short ![x, y, z]) := by
  have h := center_naturality g short ![x, y, z]
  rw [center_apply] at h
  simpa [centerVector] using h

private theorem offDiagonal_zero (x : LoopSpace M) :
    entry g 0 1 x = 0 ∧ entry g 2 3 x = 0 ∧ entry g 4 5 x = 0 := by
  have h0 := short_relation g x 0 0
  have h1 := short_relation g 0 x 0
  have h2 := short_relation g 0 0 x
  have h03 := congrFun h0 2
  have h04 := congrFun h0 4
  have h05 := congrFun h0 5
  have h20 := congrFun h2 0
  have h22 := congrFun h2 2
  have h23 := congrFun h2 3
  have h10 := congrFun h1 0
  have h11 := congrFun h1 1
  have h14 := congrFun h1 4
  simp [centerVector, coordinateCount] at h03 h04 h05 h20 h22 h23 h10 h11 h14
  grind

private theorem diagonal_eq (i : Fin 6) (x : LoopSpace M) :
    entry g i i x = entry g 0 0 x := by
  have h0 := short_relation g x 0 0
  have h2 := short_relation g 0 0 x
  have h1 := short_relation g 0 x 0
  have h00 := congrFun h0 0
  have h01 := congrFun h0 1
  have h03 := congrFun h0 3
  have h04 := congrFun h0 4
  have h02 := congrFun h0 2
  have h20 := congrFun h2 0
  have h22 := congrFun h2 2
  have h14 := congrFun h1 4
  have h21 := congrFun h2 1
  have h24 := congrFun h2 4
  have h25 := congrFun h2 5
  have h10 := congrFun h1 0
  have h12 := congrFun h1 2
  have h15 := congrFun h1 5
  have hz := offDiagonal_zero g x
  have hz' := offDiagonal_zero g ((M.map Quiver.OneLoop.loop.toPath).hom x)
  simp [centerVector, coordinateCount, hz.1, hz.2.1, hz.2.2, hz'.2.1]
    at h00 h01 h02 h03 h04 h20 h21 h22 h24 h25 h10 h12 h14 h15
  have hf0 := map_zero (N.map Quiver.OneLoop.loop.toPath).hom
  fin_cases i <;> grind

private theorem center_apply_diagonal (x : Fin 6 → LoopSpace M) (i : Fin 6) :
    component g center x i = entry g 0 0 (x i) := by
  rw [center_apply]
  fin_cases i <;> simp [offDiagonal_zero, diagonal_eq]

private theorem intertwine (x : LoopSpace M) :
    entry g 0 0 ((M.map Quiver.OneLoop.loop.toPath).hom x) =
      (N.map Quiver.OneLoop.loop.toPath).hom (entry g 0 0 x) := by
  have h := short_relation g 0 x 0
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have hz := offDiagonal_zero g x
  have hz' := offDiagonal_zero g ((M.map Quiver.OneLoop.loop.toPath).hom x)
  simp [centerVector, coordinateCount, hz.2.2, hz'.2.1, diagonal_eq] at h0 h2 h3
  grind

private theorem centerVector_injective (v : Quiver.AffineE8) :
    Function.Injective (centerVector N v) := by
  intro x y h
  funext i
  cases v with
  | center => exact congrFun h i
  | short =>
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 2
    · exact congrFun h 4
  | medium2 =>
    fin_cases i
    · exact congrFun h 4
    · exact congrFun h 5
  | medium4 =>
    fin_cases i
    · exact congrFun h 2
    · exact congrFun h 3
    · exact congrFun h 4
    · exact congrFun h 5
  | long1 =>
    fin_cases i
    · exact congrFun h 0
  | long2 =>
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
  | long3 =>
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
    · exact congrFun h 2
  | long4 =>
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
    · exact congrFun h 2
    · exact congrFun h 3
  | long5 =>
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
    · exact congrFun h 2
    · exact congrFun h 3
    · exact congrFun h 4

private theorem hom_ext_center {g h : affineE8LoopRep M ⟶ affineE8LoopRep N}
    (hc : component g center = component h center) : g = h := by
  apply NatTrans.ext
  funext v
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply centerVector_injective (N := N) v
  calc
    centerVector N v (component g v x) =
        component g center (centerVector M v x) := (center_naturality g v x).symm
    _ = component h center (centerVector M v x) := LinearMap.congr_fun hc _
    _ = centerVector N v (component h v x) := center_naturality h v x

private noncomputable def unloop : M ⟶ N :=
  Paths.liftNatTrans
    (fun _ ↦ ModuleCat.ofHom (entry g 0 0)) fun {a b} e ↦ by
      cases a
      cases b
      rw [Subsingleton.elim e Quiver.OneLoop.loop]
      exact ModuleCat.hom_ext (LinearMap.ext (intertwine g))

end Full

/-- The loop-to-flag functor is fully faithful: every morphism is coordinatewise application
of one linear map intertwining the loop actions. -/
noncomputable def fullyFaithfulAffineE8LoopFunctor :
    (affineE8LoopFunctor.{u, w, t} k).FullyFaithful where
  preimage g := unloop g
  map_preimage {M N} g := by
    apply hom_ext_center
    apply LinearMap.ext
    intro x
    funext i
    exact (center_apply_diagonal g x i).symm
  preimage_map {M N} φ := by
    apply NatTrans.ext
    funext v
    cases v
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The flag construction reflects and preserves isomorphisms. -/
@[simp] theorem nonempty_affineE8LoopRep_iso_iff :
    Nonempty (affineE8LoopRep M ≅ affineE8LoopRep N) ↔ Nonempty (M ≅ N) :=
  ⟨fun ⟨e⟩ ↦ ⟨fullyFaithfulAffineE8LoopFunctor.preimageIso e⟩,
    fun ⟨e⟩ ↦ ⟨(affineE8LoopFunctor k).mapIso e⟩⟩

/-- A loop indecomposable gives an indecomposable configuration of three flags. -/
theorem indecomposable_affineE8LoopRep (hM : Indecomposable M) :
    Indecomposable (affineE8LoopRep M) :=
  (affineE8LoopFunctor k).indecomposable_obj_of_map_bijective hM
    (fullyFaithfulAffineE8LoopFunctor.map_bijective M M)

/-- Finite representation type for the extended `E₈` quiver would imply it for the loop quiver. -/
theorem IsFiniteRepType.oneLoop_of_affineE8
    (h : IsFiniteRepType.{u, 0, 0, t} k Quiver.AffineE8) :
    IsFiniteRepType.{u, 0, w, t} k Quiver.OneLoop :=
  isFiniteRepType_of_map (fun _ ↦ False) affineE8LoopRep
    (fun _ hM hM' _ ↦ ⟨isFinDim_affineE8LoopRep hM, indecomposable_affineE8LoopRep hM'⟩)
    (fun _ _ _ _ _ _ ↦ nonempty_affineE8LoopRep_iso_iff.mp) (fun _ _ _ _ h _ ↦ h.elim) h

/-- The extended Dynkin quiver `E₈~` has infinite representation type over every field. -/
theorem not_isFiniteRepType_affineE8 (k : Type u) [Field k] :
    ¬ IsFiniteRepType.{u, 0, 0, u} k Quiver.AffineE8 :=
  fun h ↦ not_isFiniteRepType_oneLoop.{u, 0} k h.oneLoop_of_affineE8

end TauCeti
