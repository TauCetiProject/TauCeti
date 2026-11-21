/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Map
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Normal
public import TauCeti.Geometry.Symplectic.Manifold.Invariants.FixedLocus
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# The isotropy representation on the symplectic normal bundle of a fixed submanifold

Let a group `K` act on a manifold `N` by differentiable maps, and let `f : M → N` be a smooth
embedding of a submanifold of fixed points: `k • f x = f x` for every `k` and `x`. At `f x` the
differential of `y ↦ k • y` maps `T_(f x) N` to itself, and it fixes every tangent vector of the
submanifold (`TauCeti.SmoothEmbedding.mfderiv_smul_eq_self_of_mem_tangentRange`), so it descends to
the normal space `T_(f x) N / df_x (T_x M)`. This is the **isotropy representation on the normal
space** (`TauCeti.SmoothEmbedding.fixedNormalRepresentation`), Mathlib's quotient representation
`Representation.quotient` of the tangent representation `TauCeti.tangentRepresentation`. On each
fibre it is the normal map `TauCeti.SmoothEmbedding.normalMap` induced by the commuting square
`(k • ·) ∘ f = f`, so on the normal bundle `k` acts by the bundle map
`TauCeti.SmoothEmbedding.normalBundleMap`, which is smooth when the action is
(`TauCeti.SmoothEmbedding.contMDiff_fixedNormalRepresentation`): `K` acts on the normal bundle of a
submanifold of fixed points by smooth vector bundle automorphisms covering the identity.

Now let `σ` be a nondegenerate two-form on `N` preserved by the action, and let the submanifold be
symplectic. Its normal bundle is the symplectic normal bundle: each normal class has a unique
representative in the symplectic complement `(df_x (T_x M))^σ`
(`TauCeti.SmoothEmbedding.symplecticNormalRepresentative`), and `σ` induces the normal symplectic
form `TauCeti.SmoothEmbedding.symplecticNormalForm` on the normal spaces. The isotropy
representation is compatible with this structure:

* taking symplectic representatives is equivariant: the representative of `k • ν` is
  `d(k •)_(f x)` applied to the representative of `ν`
  (`TauCeti.SmoothEmbedding.symplecticNormalRepresentative_fixedNormalRepresentation`), so the
  normal representation is the restriction of the tangent representation to the symplectic
  complement of the tangent space of the submanifold;
* `K` acts by linear symplectic maps of the normal symplectic form
  (`TauCeti.SmoothEmbedding.symplecticNormalForm_fixedNormalRepresentation`);
* if every tangent vector at `f x` fixed by `K` is tangent to the submanifold, the normal
  representation has no nonzero fixed vector
  (`TauCeti.SmoothEmbedding.invariants_fixedNormalRepresentation_eq_bot`).

The last hypothesis holds on the parts `M^K_d` of the fixed set of a group of symplectic
isometries, whose tangent spaces are exactly the fixed tangent subspaces
(`IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsOfFinrank`).
So along each fixed component the normal bundle is a symplectic vector bundle on which `K` acts
fibrewise by symplectic automorphisms without nonzero fixed vectors
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_invariants_fixedNormalRepresentation_eq_bot`). For
a torus action this is the input to the decomposition of the normal spaces of the fixed components
into nonzero weights. The hypothesis that the submanifold is symplectic cannot be dropped: the
symplectic shear `(q, p) ↦ (q + p, p)` of `ℝ²` fixes the Lagrangian line `p = 0`, whose tangent
vectors are exactly the fixed tangent vectors, and the normal class `[e₂]` is fixed although `e₂`
is not.

## Main definitions

* `TauCeti.SmoothEmbedding.fixedNormalRepresentation`: the representation of `K` on the normal
  space of a submanifold of fixed points.

## Main results

* `TauCeti.SmoothEmbedding.tangentRange_le_fixedTangentSubspace`: the tangent vectors of a
  submanifold of fixed points are fixed.
* `TauCeti.SmoothEmbedding.fixedNormalRepresentation_eq_normalMap`: the normal representation is
  the normal map of the square `(k • ·) ∘ f = f`.
* `TauCeti.SmoothEmbedding.contMDiff_fixedNormalRepresentation`: it acts on the normal bundle by
  smooth bundle maps.
* `TauCeti.SmoothEmbedding.symplecticNormalRepresentative_fixedNormalRepresentation`: symplectic
  representatives are equivariant.
* `TauCeti.SmoothEmbedding.symplecticNormalForm_fixedNormalRepresentation`: the normal
  representation preserves the normal symplectic form.
* `TauCeti.SmoothEmbedding.invariants_fixedNormalRepresentation_eq_bot`: it has no nonzero fixed
  vector when the submanifold contains every fixed tangent direction.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_invariants_fixedNormalRepresentation_eq_bot`: this
  applies to the parts `M^K_d` of the fixed set of a group of symplectic isometries.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (fixed points of a group of symplectic isometries).
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15
  (the normal bundles of the fixed components and their weights).
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
-/

public noncomputable section

open Bundle MulAction Filter
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {K : Type*} [Group K] [MulAction K N]
  (f : SmoothEmbedding I J n M N) (hf : ∀ (k : K) (x : M), k • f x = f x)

/-! ### The normal representation -/

section Representation

include hf in
/-- On a submanifold of fixed points, the differential of the action of `k` fixes every tangent
vector of the submanifold. -/
theorem mfderiv_smul_eq_self_of_mem_tangentRange {k : K} {x : M}
    (hd : MDifferentiableAt J J (fun y : N ↦ k • y) (f x)) (hn : n ≠ 0)
    {w : TangentSpace J (f x)} (hw : w ∈ f.tangentRange x hn) :
    mfderiv J J (fun y : N ↦ k • y) (f x) w = w := by
  obtain ⟨u, rfl⟩ := (f.mem_tangentRange_iff x hn w).1 hw
  have hc := mfderiv_comp_apply x hd (f.contMDiff.mdifferentiableAt hn) u
  rw [show (fun y : N ↦ k • y) ∘ f = f from funext (hf k)] at hc
  exact hc.symm

include hf in
/-- **The tangent vectors of a submanifold of fixed points are fixed.** For an action by
differentiable maps, the tangent space of a submanifold of fixed points lies in the fixed tangent
subspace. -/
theorem tangentRange_le_fixedTangentSubspace (x : M) (hn : n ≠ 0)
    (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x)) :
    f.tangentRange x hn ≤ fixedTangentSubspace J K (f x) :=
  fun _ hw ↦ mem_fixedTangentSubspace.2 fun k _ ↦
    f.mfderiv_smul_eq_self_of_mem_tangentRange hf (hd k) hn hw

/-- The tangent representation of `K` at the fixed point `f x`, the stabilizer of `f x` being all
of `K`. -/
private def fixedTangentRepresentation (x : M)
    (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x)) :
    Representation ℝ K (TangentSpace J (f x)) :=
  (tangentRepresentation (I := J) (x := f x) fun g _ ↦ hd g).toRepresentation.comp
    ((MonoidHom.id K).codRestrict (stabilizer K (f x)) fun k ↦ hf k x)

private theorem fixedTangentRepresentation_apply (x : M)
    (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x)) (k : K)
    (w : TangentSpace J (f x)) :
    f.fixedTangentRepresentation hf x hd k w = mfderiv J J (fun y : N ↦ k • y) (f x) w := by
  rw [fixedTangentRepresentation, MonoidHom.comp_apply, ContRepresentation.toRepresentation_apply,
    tangentRepresentation_apply]
  -- The element of the stabilizer is `k` itself.
  rfl

/-- The **isotropy representation on the normal space** of a submanifold of fixed points: `k`
acts on the class of a tangent vector `w` at `f x` as the class of `d(k •)_(f x) w`. It is the
quotient of the tangent representation of `K` at the fixed point `f x` by the tangent space of the
submanifold, which it fixes. -/
def fixedNormalRepresentation (x : M) (hn : n ≠ 0)
    (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x)) :
    Representation ℝ K (f.NormalSpace x hn) :=
  (f.fixedTangentRepresentation hf x hd).quotient (f.tangentRange x hn) fun k w hw ↦ by
    rw [Submodule.mem_comap, fixedTangentRepresentation_apply,
      f.mfderiv_smul_eq_self_of_mem_tangentRange hf (hd k) hn hw]
    exact hw

/-- The normal representation acts on the class of `w` as the class of `d(k •)_(f x) w`. -/
@[simp]
theorem fixedNormalRepresentation_normalClass
    (x : M) (hn : n ≠ 0) (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x))
    (k : K) (w : TangentSpace J (f x)) :
    f.fixedNormalRepresentation hf x hn hd k (f.normalClass x hn w) =
      f.normalClass x hn (mfderiv J J (fun y : N ↦ k • y) (f x) w) := by
  rw [normalClass_def, ← fixedTangentRepresentation_apply]
  -- The quotient representation acts on `mkQ w` by `Submodule.mapQ`, which is `mkQ` of the image.
  rfl

/-- The normal representation of `k` is the normal map induced by the commuting square
`(k • ·) ∘ f = f ∘ id`. -/
theorem fixedNormalRepresentation_eq_normalMap
    (x : M) (hn : n ≠ 0) (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x))
    (k : K) :
    f.fixedNormalRepresentation hf x hn hd k =
      (f.normalMap f hn hn (u := _root_.id) (v := fun y : N ↦ k • y) (x := x)
        (EventuallyEq.of_eq (funext (hf k)))).toLinearMap := by
  ext ν
  obtain ⟨w, rfl⟩ := f.normalClass_surjective x hn ν
  simp only [fixedNormalRepresentation_normalClass, ContinuousLinearMap.coe_coe,
    normalMap_normalClass]
  -- `tangentSpaceCast` identifies `T_(k • f x) N` with `T_(f x) N`, two copies of the model space.
  rfl

/-- The action of `k` on the normal bundle, the bundle map induced by the square
`(k • ·) ∘ f = f ∘ id`, acts on each fibre by the normal representation. -/
theorem normalBundleMap_smul_apply (hn : n ≠ 0)
    (hd : ∀ (x : M) (k : K), MDifferentiableAt J J (fun y : N ↦ k • y) (f x)) (k : K)
    {P : Type*} (p : TotalSpace P fun x ↦ f.NormalSpace x hn) :
    f.normalBundleMap (K := P) (K' := P) f hn hn (u := _root_.id) (v := fun y : N ↦ k • y)
        (funext (hf k)) p =
      ⟨p.proj, f.fixedNormalRepresentation hf p.proj hn (hd p.proj) k p.snd⟩ := by
  rw [normalBundleMap_apply, fixedNormalRepresentation_eq_normalMap]
  -- The base map of the square is the identity.
  rfl

/-- **`K` acts on the normal bundle of a submanifold of fixed points by smooth bundle maps.** If
`K` acts by `C^(r + 1)` maps and the embedding is `C^(r + 1)`, then each `k` acts on the normal
bundle, fibrewise by the normal representation, by a `C^r` map covering the identity. -/
theorem contMDiff_fixedNormalRepresentation [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {r : ℕ∞ω}
    [IsManifold I (r + 1) M] [IsManifold J (r + 1) N] [ContMDiffConstSMul J (r + 1) K N]
    (hn : n ≠ 0) (hrn : r + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) (k : K) :
    haveI : IsManifold I 1 M := .of_le (n := r + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := r + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) r
      fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
        (⟨p.proj, f.fixedNormalRepresentation hf p.proj hn
          (fun g ↦ ((contMDiff_const_smul (I := J) (n := r + 1) g).of_le
            (le_add_self : (1 : ℕ∞ω) ≤ r + 1)).mdifferentiableAt one_ne_zero)
          k p.snd⟩ : TotalSpace P fun x ↦ f.NormalSpace x hn) := by
  have : IsManifold I 1 M := .of_le (n := r + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := r + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  have hc := f.contMDiff_normalBundleMap (P := P) (P' := P) (J := J) (J' := J) f hn hn hrn hrn
    hdim hdim (u := _root_.id) (v := fun y : N ↦ k • y) (contMDiff_const_smul k) (funext (hf k))
  refine hc.congr fun p ↦ ?_
  rw [f.normalBundleMap_smul_apply hf hn fun _ g ↦
    ((contMDiff_const_smul (I := J) (n := r + 1) g).of_le
      (le_add_self : (1 : ℕ∞ω) ≤ r + 1)).mdifferentiableAt one_ne_zero]

end Representation

/-! ### Compatibility with the symplectic normal structure -/

section Symplectic

open SmoothTwoForm

variable [FiniteDimensional ℝ V] [IsManifold J ∞ N] [ContMDiffConstSMul J ∞ K N]
  {σ : SmoothTwoForm J N} {hσ : σ.IsNondegenerate}
  (hσK : ∀ k : K, SmoothForm.mpullback (fun y : N ↦ k • y) (contMDiff_const_smul k) σ = σ)

include hσK in
/-- **Symplectic representatives are equivariant.** For an action preserving `σ` and a symplectic
submanifold of fixed points, the symplectic representative of `k • ν` is the image under
`d(k •)_(f x)` of the symplectic representative of `ν`. -/
theorem symplecticNormalRepresentative_fixedNormalRepresentation
    (h : hσ.HasSymplecticTangentImages I f)
    (x : M) (hn : n ≠ 0) (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x))
    (k : K) (ν : f.NormalSpace x hn) :
    f.symplecticNormalRepresentative h x hn (f.fixedNormalRepresentation hf x hn hd k ν) =
      mfderiv J J (fun y : N ↦ k • y) (f x) (f.symplecticNormalRepresentative h x hn ν) := by
  set w := f.symplecticNormalRepresentative h x hn ν
  refine (f.symplecticNormalRepresentative_eq_iff h x hn _ _).2 ⟨?_, ?_⟩
  · -- `d(k •)` fixes the tangent space and preserves `σ_(f x)`, so it preserves the complement.
    refine SymplecticForm.mem_orthogonal_iff.2 fun u hu ↦ ?_
    have hsymp := hσ.symplecticFormAt_tangentRepresentation (fun g _ ↦ hσK g)
      (fun g _ ↦ hd g) ⟨k, hf k x⟩ u w
    rw [tangentRepresentation_apply] at hsymp
    rw [← f.mfderiv_smul_eq_self_of_mem_tangentRange hf (hd k) hn hu]
    exact hsymp.trans (SymplecticForm.mem_orthogonal_iff.1
      (f.symplecticNormalRepresentative_mem_orthogonal h x hn ν) u hu)
  · rw [← fixedNormalRepresentation_normalClass, normalClass_symplecticNormalRepresentative]

include hσK in
/-- **The normal representation is symplectic.** For an action preserving `σ` and a symplectic
submanifold of fixed points, each `k` acts on the normal space by a linear symplectic map of the
normal symplectic form. -/
theorem symplecticNormalForm_fixedNormalRepresentation
    (h : hσ.HasSymplecticTangentImages I f)
    (x : M) (hn : n ≠ 0) (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x))
    (k : K) (ν μ : f.NormalSpace x hn) :
    f.symplecticNormalForm h x hn (f.fixedNormalRepresentation hf x hn hd k ν)
        (f.fixedNormalRepresentation hf x hn hd k μ) =
      f.symplecticNormalForm h x hn ν μ := by
  have hsymp := hσ.symplecticFormAt_tangentRepresentation (fun g _ ↦ hσK g)
    (fun g _ ↦ hd g) ⟨k, hf k x⟩ (f.symplecticNormalRepresentative h x hn ν)
    (f.symplecticNormalRepresentative h x hn μ)
  rw [tangentRepresentation_apply] at hsymp
  simp only [symplecticNormalForm_apply,
    f.symplecticNormalRepresentative_fixedNormalRepresentation hf hσK h]
  simp only [IsNondegenerate.symplecticFormAt_apply] at hsymp
  exact hsymp

include hσK in
/-- **The normal representation has no nonzero fixed vector.** For an action preserving `σ` and a
symplectic submanifold of fixed points containing every fixed tangent direction at `f x`, the
only normal vector at `x` fixed by every element of `K` is zero. -/
theorem invariants_fixedNormalRepresentation_eq_bot
    (h : hσ.HasSymplecticTangentImages I f)
    (x : M) (hn : n ≠ 0) (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x))
    (hfix : fixedTangentSubspace J K (f x) ≤ f.tangentRange x hn) :
    (f.fixedNormalRepresentation hf x hn hd).invariants = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun ν hν ↦ ?_
  set w := f.symplecticNormalRepresentative h x hn ν
  -- The representative `w` of a fixed class is a fixed tangent vector, hence tangent.
  have hw : w ∈ f.tangentRange x hn := hfix <| mem_fixedTangentSubspace.2 fun k _ ↦ by
    rw [← f.symplecticNormalRepresentative_fixedNormalRepresentation hf hσK h x hn hd,
      hν k]
  -- It also lies in the symplectic complement of the tangent space, which meets it in zero.
  have hw0 : w = 0 := Submodule.disjoint_def.1 (SymplecticForm.isSymplectic_iff_disjoint.1
    (IsNondegenerate.hasSymplecticTangentImages_iff_forall.1 h x)) w hw
      (f.symplecticNormalRepresentative_mem_orthogonal h x hn ν)
  have hνw : f.normalClass x hn w = ν := f.normalClass_symplecticNormalRepresentative h x hn ν
  rw [← hνw, hw0, map_zero]

end Symplectic

end TauCeti.SmoothEmbedding

/-! ### The fixed locus of a group of symplectic isometries -/

namespace TauCeti.SmoothTwoForm

open MulAction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul 𝓘(ℝ, E) ∞ K M]
  {σ : SmoothTwoForm 𝓘(ℝ, E) M}

/-- **The normal representations along the fixed locus of a group of symplectic isometries.** For
a group acting by isometries preserving a nondegenerate two-form `σ` and a subspace `L` of the
model of dimension `d`, the part `M^K_d` of the fixed set is a symplectic submanifold modelled on
`L` whose normal representation at every point has no nonzero fixed vector. -/
theorem IsNondegenerate.exists_invariants_fixedNormalRepresentation_eq_bot
    (hK : ∀ (k : K) (x : M) (u w : TangentSpace 𝓘(ℝ, E) x),
      inner ℝ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (k • ·) x u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (k • ·) x w) =
        inner ℝ u w)
    (hσK : ∀ k : K, SmoothForm.mpullback (fun y : M ↦ k • y) (contMDiff_const_smul k) σ = σ)
    (hσ : σ.IsNondegenerate) {d : ℕ} {L : Submodule ℝ E} (hL : Module.finrank ℝ L = d) :
    ∃ C : ChartedSpace L (fixedPointsOfFinrank 𝓘(ℝ, E) K M d), letI := C
      ∃ (_ : IsManifold 𝓘(ℝ, L) ∞ (fixedPointsOfFinrank 𝓘(ℝ, E) K M d))
        (hemb : hσ.IsSymplecticSubmanifoldEmbedding 𝓘(ℝ, L)
          (Subtype.val : fixedPointsOfFinrank 𝓘(ℝ, E) K M d → M)),
        ∀ y, ((SmoothEmbedding.ofIsSmoothEmbedding (I := 𝓘(ℝ, L)) (J := 𝓘(ℝ, E)) (n := ∞) _
          hemb.isSmoothEmbedding).fixedNormalRepresentation
          (fun (k : K) y ↦ by simpa using fixedPointsOfFinrank_subset_fixedPoints d y.property k) y
          (by simp) fun k ↦ ContMDiffConstSMul.mdifferentiable_const_smul (n := ∞) (by simp) k _
          ).invariants = ⊥ := by
  obtain ⟨C, hman, hemb, hrange⟩ :=
    hσ.exists_isSymplecticSubmanifoldEmbedding_fixedPointsOfFinrank hK hσK hL
  let := C
  refine ⟨C, hman, hemb, fun y ↦ ?_⟩
  refine SmoothEmbedding.invariants_fixedNormalRepresentation_eq_bot (hσ := hσ) _ _ hσK ?_ y _ _ ?_
  · simpa using hemb.hasSymplecticTangentImages
  · -- Replace the bundled embedding by its underlying inclusion, on which `hrange` is stated.
    rw [SmoothEmbedding.tangentRange]
    generalize hG : ⇑(SmoothEmbedding.ofIsSmoothEmbedding (I := 𝓘(ℝ, L)) (J := 𝓘(ℝ, E))
      (n := ∞) _ hemb.isSmoothEmbedding) = G
    rw [SmoothEmbedding.coe_ofIsSmoothEmbedding] at hG
    subst hG
    exact (hrange y).ge

end TauCeti.SmoothTwoForm
