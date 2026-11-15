/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
import TauCeti.Algebra.DirectSum.HomogeneousExtend
import TauCeti.Algebra.DirectSum.Internal

/-!
# Coinduced graded modules and enough injectives

For a `ℤ`-graded `k`-algebra `A` decomposed by `𝒜` and an ungraded left `A`-module `N`, the
**coinduced** graded module has underlying `k`-module `⨁ p : ℤ, N`, with degree-`p` piece given by
the `p`-th summand and homogeneous scalar multiplication shifting summands: an element `a ∈ 𝒜 q`
sends `(p, y)` to `(q + p, a • y)`.

Summing the homogeneous coordinates defines an `A`-linear counit `toModuleCat (coind N) ⟶ N`.
Conversely, since every element `m` of an internally graded `𝒜`-module `M` has only finitely many
nonzero homogeneous components `m_p`, any `A`-linear map `f : M ⟶ N` lifts uniquely to a degree-zero
graded morphism `M ⟶ coind N` whose `p`-th coordinate on `m` is `f (m_p)`. This exhibits
`coindFunctor 𝒜` as right adjoint to the forgetful functor `toModuleCat`.

Because `toModuleCat` preserves and reflects monomorphisms and `ModuleCat A` has enough injectives,
the adjunction transfers injective objects and enough injectives to `GradedModuleCat 𝒜`.

## Main definitions

* `TauCeti.GradedModuleCat.coindFunctor`: the right adjoint `ModuleCat A ⥤ GradedModuleCat 𝒜` to
  forgetting the grading.
* `TauCeti.GradedModuleCat.coindCounit` and `TauCeti.GradedModuleCat.coindLift`: the `A`-linear
  counit `toModuleCat ((coindFunctor 𝒜).obj N) ⟶ N` and the graded lift
  `M ⟶ (coindFunctor 𝒜).obj N` of an ungraded map `toModuleCat.obj M ⟶ N`.
* `TauCeti.GradedModuleCat.coindHomEquiv`: the additive universal-property equivalence
  `(M ⟶ (coindFunctor 𝒜).obj N) ≃+ (toModuleCat.obj M ⟶ N)`.
* `TauCeti.GradedModuleCat.toModuleCatCoindAdj`: the adjunction `toModuleCat ⊣ coindFunctor 𝒜`.

## Main results

* `TauCeti.GradedModuleCat.coind_hom_ext`: graded morphisms into `(coindFunctor 𝒜).obj N` are
  determined by their ungraded composites with `coindCounit`.
* `TauCeti.GradedModuleCat.injective_coindFunctor_obj`: `coindFunctor 𝒜` preserves injective
  objects.
* `TauCeti.GradedModuleCat.enoughInjectives` and the `[Small.{v} A]` instance
  `EnoughInjectives (GradedModuleCat.{v} 𝒜)`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Lecture Notes in Mathematics
  **1836**, Springer (2004), Section 2.2 (the right adjoint to forgetting a group grading) and
  Section 2.3 (enough injectives in categories of graded modules).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- Wrapper isolating the `k`-module structure on a summand of `⨁ p : ℤ, N` from the unshifted
`A`-module structure on `N`. -/
@[ext]
private structure CoindSummand (k : Type uk) {A : Type uA} [Ring A] (N : ModuleCat.{v} A) where
  val : N

private theorem coindSummand_val_injective {k : Type uk} (N : ModuleCat.{v} A) :
    Function.Injective (CoindSummand.val (k := k) (N := N)) :=
  fun _ _ ↦ CoindSummand.ext

private instance (N : ModuleCat.{v} A) : Zero (CoindSummand k N) := ⟨⟨0⟩⟩
private instance (N : ModuleCat.{v} A) : Add (CoindSummand k N) := ⟨fun x y ↦ ⟨x.val + y.val⟩⟩
private instance (N : ModuleCat.{v} A) : Neg (CoindSummand k N) := ⟨fun x ↦ ⟨-x.val⟩⟩
private instance (N : ModuleCat.{v} A) : Sub (CoindSummand k N) := ⟨fun x y ↦ ⟨x.val - y.val⟩⟩
private instance (N : ModuleCat.{v} A) : SMul ℕ (CoindSummand k N) := ⟨fun n x ↦ ⟨n • x.val⟩⟩
private instance (N : ModuleCat.{v} A) : SMul ℤ (CoindSummand k N) := ⟨fun n x ↦ ⟨n • x.val⟩⟩
private instance (N : ModuleCat.{v} A) : SMul k (CoindSummand k N) :=
  ⟨fun c x ↦ ⟨algebraMap k A c • x.val⟩⟩

omit [CommRing k] [Algebra k A] in
@[simp]
private theorem coindSummand_val_zero (N : ModuleCat.{v} A) :
    (0 : CoindSummand k N).val = 0 :=
  rfl

omit [CommRing k] [Algebra k A] in
@[simp]
private theorem coindSummand_val_add (N : ModuleCat.{v} A) (x y : CoindSummand k N) :
    (x + y).val = x.val + y.val :=
  rfl

@[simp]
private theorem coindSummand_val_smul (N : ModuleCat.{v} A) (c : k) (x : CoindSummand k N) :
    (c • x).val = algebraMap k A c • x.val :=
  rfl

private instance (N : ModuleCat.{v} A) : AddCommGroup (CoindSummand k N) :=
  Function.Injective.addCommGroup CoindSummand.val (coindSummand_val_injective N)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

private instance (N : ModuleCat.{v} A) : Module k (CoindSummand k N) where
  one_smul _ := CoindSummand.ext (by simp)
  mul_smul _ _ _ := CoindSummand.ext (by simp [mul_smul])
  smul_zero _ := CoindSummand.ext (by simp)
  smul_add _ _ _ := CoindSummand.ext (by simp [smul_add])
  add_smul _ _ _ := CoindSummand.ext (by simp [add_smul])
  zero_smul _ := CoindSummand.ext (by simp)

private def coindSummandLsmul (k : Type uk) [CommRing k] [Algebra k A]
    (N : ModuleCat.{v} A) : A →ₐ[k] Module.End k (CoindSummand k N) where
  toFun a :=
    { toFun := fun y ↦ ⟨a • y.val⟩
      map_add' := fun x y ↦ CoindSummand.ext (smul_add a x.val y.val)
      map_smul' := fun c y ↦ CoindSummand.ext <| by
        simp only [coindSummand_val_smul, RingHom.id_apply]
        rw [← mul_smul, ← Algebra.commutes, mul_smul] }
  map_one' := by ext y; exact one_smul A y.val
  map_mul' a b := by ext y; exact mul_smul a b y.val
  map_zero' := by ext y; exact zero_smul A y.val
  map_add' a b := by ext y; exact add_smul a b y.val
  commutes' _ := by ext; rfl

private def mapCoindSummand (k : Type uk) [CommRing k] [Algebra k A]
    {N₁ N₂ : ModuleCat.{v} A} (g : N₁ ⟶ N₂) :
    CoindSummand k N₁ →ₗ[k] CoindSummand k N₂ where
  toFun y := ⟨g.hom y.val⟩
  map_add' x y := CoindSummand.ext (g.hom.map_add x.val y.val)
  map_smul' c y := CoindSummand.ext (g.hom.map_smul (algebraMap k A c) y.val)

/-- Homogeneous action of `a ∈ 𝒜 q` on `⨁ p : ℤ, N`, shifting summand `p` to `q + p`. -/
private def coindHomogeneousEnd (N : ModuleCat.{v} A) (q : ℤ) :
    𝒜 q →ₗ[k] Module.End k (⨁ _ : ℤ, CoindSummand k N) where
  toFun a := DirectSum.toModule k ℤ (⨁ _ : ℤ, CoindSummand k N) fun p ↦
    (DirectSum.lof k ℤ (fun _ ↦ CoindSummand k N) (q + p)).comp
      (coindSummandLsmul k N (a : A))
  map_add' a b := by
    apply DirectSum.linearMap_ext k
    intro p
    ext y
    simp [map_add]
  map_smul' c a := by
    apply DirectSum.linearMap_ext k
    intro p
    ext y
    simp [map_smul]

/-- The `k`-linear action map `A →ₗ[k] End_k(⨁ p : ℤ, N)` extended from homogeneous pieces. -/
private def coindEndLinear (N : ModuleCat.{v} A) :
    A →ₗ[k] Module.End k (⨁ _ : ℤ, CoindSummand k N) :=
  DirectSum.homogeneousExtend 𝒜 (coindHomogeneousEnd 𝒜 N)

private theorem coindEndLinear_of_mem (N : ModuleCat.{v} A) {q : ℤ} {a : A} (ha : a ∈ 𝒜 q)
    (p : ℤ) (y : N) :
    coindEndLinear 𝒜 N a (DirectSum.lof k ℤ (fun _ ↦ CoindSummand k N) p ⟨y⟩) =
      DirectSum.lof k ℤ (fun _ ↦ CoindSummand k N) (q + p) ⟨a • y⟩ := by
  rw [coindEndLinear, DirectSum.homogeneousExtend_of_mem 𝒜 _ ha]
  simp [coindHomogeneousEnd, coindSummandLsmul]

/-- The `k`-algebra homomorphism `A →ₐ[k] End_k(⨁ p : ℤ, N)` defining the graded `A`-action. -/
private def coindEndAlgHom (N : ModuleCat.{v} A) :
    A →ₐ[k] Module.End k (⨁ _ : ℤ, CoindSummand k N) :=
  AlgHom.ofLinearMap (coindEndLinear 𝒜 N)
    (by
      apply DirectSum.linearMap_ext k
      intro p
      refine LinearMap.ext fun ⟨y⟩ ↦ ?_
      -- Unfold `1 : Module.End k _` to the identity on the `p`-th summand.
      change coindEndLinear 𝒜 N 1 (DirectSum.lof k ℤ _ p ⟨y⟩) = DirectSum.lof k ℤ _ p ⟨y⟩
      rw [coindEndLinear_of_mem 𝒜 N (SetLike.one_mem_graded 𝒜), zero_add, one_smul])
    (fun a b ↦ by
      induction a using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | @homogeneous q a =>
        induction b using DirectSum.Decomposition.inductionOn 𝒜 with
        | zero => simp
        | @homogeneous r b =>
          apply DirectSum.linearMap_ext k
          intro p
          refine LinearMap.ext fun ⟨y⟩ ↦ ?_
          -- Unfold multiplication in `Module.End k _` to function composition.
          change coindEndLinear 𝒜 N ((a : A) * (b : A)) (DirectSum.lof k ℤ _ p ⟨y⟩) =
            coindEndLinear 𝒜 N (a : A) (coindEndLinear 𝒜 N (b : A) (DirectSum.lof k ℤ _ p ⟨y⟩))
          rw [coindEndLinear_of_mem 𝒜 N (SetLike.GradedMul.mul_mem a.2 b.2),
            coindEndLinear_of_mem 𝒜 N b.2, coindEndLinear_of_mem 𝒜 N a.2, mul_smul, add_assoc]
        | add b₁ b₂ hb₁ hb₂ => simp [mul_add, hb₁, hb₂]
      | add a₁ a₂ ha₁ ha₂ => simp [add_mul, ha₁, ha₂])

/-- Construct the coinduced graded `𝒜`-module of an `A`-module `N`. -/
private def coindObj (N : ModuleCat.{v} A) : GradedModuleCat.{v} 𝒜 :=
  letI : Module A (⨁ _ : ℤ, CoindSummand k N) :=
    Module.compHom (⨁ _ : ℤ, CoindSummand k N) (coindEndAlgHom 𝒜 N).toRingHom
  haveI : IsScalarTower k A (⨁ _ : ℤ, CoindSummand k N) :=
    IsScalarTower.of_algebraMap_smul fun c z ↦
      congrArg (fun f : Module.End k _ ↦ f z) ((coindEndAlgHom 𝒜 N).commutes c)
  let G : InternalGrading k (⨁ _ : ℤ, CoindSummand k N) ℤ :=
    InternalGrading.ofDecomposition
      (_root_.DirectSum.summand k (fun _ : ℤ ↦ CoindSummand k N))
  haveI : SetLike.GradedSMul 𝒜 G.piece := ⟨fun {q p} a z ha hz ↦ by
    rw [InternalGrading.ofDecomposition_piece] at hz ⊢
    obtain ⟨⟨y⟩, rfl⟩ := _root_.DirectSum.mem_summand.mp hz
    rw [← DirectSum.lof_eq_of k]
    -- Unfold the `A`-action and `ℤ`-vadd to `coindEndLinear` and `+`.
    change coindEndLinear 𝒜 N a _ ∈ _root_.DirectSum.summand k _ (q + p)
    rw [coindEndLinear_of_mem 𝒜 N ha]
    exact _root_.DirectSum.lof_mem_summand (q + p) _⟩
  { carrier := ⨁ _ : ℤ, CoindSummand k N
    grading := G }

private theorem coindObj_piece (N : ModuleCat.{v} A) (p : ℤ) :
    (coindObj 𝒜 N).grading.piece p =
      _root_.DirectSum.summand k (fun _ : ℤ ↦ CoindSummand k N) p :=
  congrFun
    (InternalGrading.ofDecomposition_piece
      (_root_.DirectSum.summand k (fun _ : ℤ ↦ CoindSummand k N))) p

private def coindMapLinear (k : Type uk) [CommRing k] [Algebra k A]
    {N₁ N₂ : ModuleCat.{v} A} (g : N₁ ⟶ N₂) :
    (⨁ _ : ℤ, CoindSummand k N₁) →ₗ[k] ⨁ _ : ℤ, CoindSummand k N₂ :=
  DirectSum.lmap fun _ : ℤ ↦ mapCoindSummand k g

private theorem coindMapLinear_id (N : ModuleCat.{v} A) :
    coindMapLinear k (𝟙 N) = LinearMap.id := by
  apply DirectSum.linearMap_ext k
  intro p
  refine LinearMap.ext fun ⟨y⟩ ↦ ?_
  simp [coindMapLinear, mapCoindSummand]

private theorem coindMapLinear_comp {N₁ N₂ N₃ : ModuleCat.{v} A} (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃) :
    coindMapLinear k (f ≫ g) = (coindMapLinear k g).comp (coindMapLinear k f) := by
  apply DirectSum.linearMap_ext k
  intro p
  refine LinearMap.ext fun ⟨y⟩ ↦ ?_
  simp [coindMapLinear, mapCoindSummand]

private theorem coindMapLinear_add {N₁ N₂ : ModuleCat.{v} A} (f g : N₁ ⟶ N₂) :
    coindMapLinear k (f + g) = coindMapLinear k f + coindMapLinear k g := by
  apply DirectSum.linearMap_ext k
  intro p
  refine LinearMap.ext fun ⟨y⟩ ↦ ?_
  simp only [coindMapLinear, LinearMap.comp_apply, LinearMap.add_apply, DirectSum.lmap_lof,
    mapCoindSummand, LinearMap.coe_mk, AddHom.coe_mk, ModuleCat.hom_add, ← map_add]
  rfl

/-- Map an `A`-linear map `g : N₁ ⟶ N₂` componentwise across `coindObj`. -/
private def coindMap {N₁ N₂ : ModuleCat.{v} A} (g : N₁ ⟶ N₂) :
    coindObj 𝒜 N₁ ⟶ coindObj 𝒜 N₂ :=
  ofHom (M := coindObj 𝒜 N₁) (N := coindObj 𝒜 N₂)
    { toFun := fun z ↦ coindMapLinear k g z
      map_add' := fun x y ↦ (coindMapLinear k g).map_add x y
      map_smul' := fun a z ↦ by
        let z' : ⨁ _ : ℤ, CoindSummand k N₁ := z
        -- Unfold the `A`-actions on `coindObj` to `coindEndLinear` on `z'`.
        change coindMapLinear k g (coindEndLinear 𝒜 N₁ a z') =
          coindEndLinear 𝒜 N₂ a (coindMapLinear k g z')
        induction a using DirectSum.Decomposition.inductionOn 𝒜 with
        | zero => simp
        | @homogeneous q a =>
          induction z' using DirectSum.induction_on with
          | zero => simp
          | of p y =>
            rcases y with ⟨y⟩
            rw [← DirectSum.lof_eq_of k, coindEndLinear_of_mem 𝒜 N₁ a.2, coindMapLinear,
              DirectSum.lmap_lof, DirectSum.lmap_lof]
            simp only [mapCoindSummand, LinearMap.coe_mk, AddHom.coe_mk, g.hom.map_smul,
              coindEndLinear_of_mem 𝒜 N₂ a.2]
          | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
        | add a₁ a₂ ha₁ ha₂ => simp [ha₁, ha₂] }
    (LinearMap.isHomogeneous_def.mpr fun p z hz ↦ by
      rw [add_zero]
      rw [coindObj_piece] at hz ⊢
      obtain ⟨y, rfl⟩ := _root_.DirectSum.mem_summand.mp hz
      rw [← DirectSum.lof_eq_of k]
      -- Unfold the underlying map to `coindMapLinear`.
      change coindMapLinear k g _ ∈ _
      rw [coindMapLinear, DirectSum.lmap_lof]
      exact _root_.DirectSum.lof_mem_summand p _)

/-- The **coinduction functor** `ModuleCat A ⥤ GradedModuleCat 𝒜`, right adjoint to forgetting
the internal grading. -/
def coindFunctor : ModuleCat.{v} A ⥤ GradedModuleCat.{v} 𝒜 where
  obj := coindObj 𝒜
  map := coindMap 𝒜
  map_id N := by
    apply hom_ext
    apply LinearMap.ext
    intro z
    exact DFunLike.congr_fun (coindMapLinear_id (k := k) N) z
  map_comp f g := by
    apply hom_ext
    apply LinearMap.ext
    intro z
    exact DFunLike.congr_fun (coindMapLinear_comp (k := k) f g) z

/-- Coinduction is an additive functor. -/
instance : (coindFunctor.{v} 𝒜).Additive where
  map_add {N₁ N₂ f g} := by
    delta coindFunctor
    apply hom_ext
    apply LinearMap.ext
    intro z
    exact DFunLike.congr_fun (coindMapLinear_add (k := k) f g) z

private def coindSummandValAddHom (k : Type uk) (N : ModuleCat.{v} A) :
    CoindSummand k N →+ N where
  toFun := CoindSummand.val
  map_zero' := rfl
  map_add' _ _ := rfl

private def coindCounitAddHom (k : Type uk) (N : ModuleCat.{v} A) :
    (⨁ _ : ℤ, CoindSummand k N) →+ N :=
  DirectSum.toAddMonoid fun _ ↦ coindSummandValAddHom k N

private theorem coindCounitAddHom_endLinear (N : ModuleCat.{v} A) (a : A)
    (z : ⨁ _ : ℤ, CoindSummand k N) :
    coindCounitAddHom k N (coindEndLinear 𝒜 N a z) = a • coindCounitAddHom k N z := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q a =>
    induction z using DirectSum.induction_on with
    | zero => simp
    | of p y =>
      rcases y with ⟨y⟩
      rw [← DirectSum.lof_eq_of k, coindEndLinear_of_mem 𝒜 N a.2]
      simp [coindCounitAddHom, coindSummandValAddHom, DirectSum.lof_eq_of]
    | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
  | add a₁ a₂ ha₁ ha₂ => simp [add_smul, ha₁, ha₂]

/-- The ungraded `A`-linear counit `toModuleCat ((coindFunctor 𝒜).obj N) ⟶ N`, summing homogeneous
coordinates in `N`. -/
def coindCounit (N : ModuleCat.{v} A) :
    toModuleCat.obj ((coindFunctor 𝒜).obj N) ⟶ N :=
  ModuleCat.ofHom
    { toFun := fun z ↦ by
        delta coindFunctor at z
        exact coindCounitAddHom k N z
      map_add' := fun x y ↦ by
        delta coindFunctor at x y
        exact (coindCounitAddHom k N).map_add x y
      map_smul' := fun a z ↦ by
        delta coindFunctor at z
        exact coindCounitAddHom_endLinear 𝒜 N a z }

private theorem coindCounitAddHom_mapLinear {N₁ N₂ : ModuleCat.{v} A} (g : N₁ ⟶ N₂)
    (z : ⨁ _ : ℤ, CoindSummand k N₁) :
    coindCounitAddHom k N₂ (coindMapLinear k g z) = g.hom (coindCounitAddHom k N₁ z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    rcases y with ⟨y⟩
    rw [← DirectSum.lof_eq_of k, coindMapLinear, DirectSum.lmap_lof]
    simp [coindCounitAddHom, coindSummandValAddHom, mapCoindSummand, DirectSum.lof_eq_of]
  | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]

private theorem toModuleCat_map_coindFunctor_comp_coindCounit {N₁ N₂ : ModuleCat.{v} A}
    (g : N₁ ⟶ N₂) :
    toModuleCat.map ((coindFunctor 𝒜).map g) ≫ coindCounit 𝒜 N₂ = coindCounit 𝒜 N₁ ≫ g := by
  delta coindFunctor coindCounit
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact coindCounitAddHom_mapLinear (k := k) g z

private def toCoindSummandLinear {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) : M →ₗ[k] CoindSummand k N where
  toFun m := ⟨f.hom m⟩
  map_add' x y := CoindSummand.ext (f.hom.map_add x y)
  map_smul' c m := CoindSummand.ext <| by
    simp only [coindSummand_val_smul, RingHom.id_apply]
    rw [← algebraMap_smul A c m]
    exact f.hom.map_smul (algebraMap k A c) m

private def coindLiftLinear {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) : M →ₗ[k] ⨁ _ : ℤ, CoindSummand k N :=
  DirectSum.homogeneousExtend M.grading.piece fun p ↦
    (DirectSum.lof k ℤ (fun _ ↦ CoindSummand k N) p).comp
      ((toCoindSummandLinear 𝒜 f).comp (M.grading.piece p).subtype)

private theorem coindLiftLinear_smul {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) (a : A) (m : M) :
    coindLiftLinear 𝒜 f (a • m) = coindEndLinear 𝒜 N a (coindLiftLinear 𝒜 f m) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q a =>
    induction m using DirectSum.Decomposition.inductionOn M.grading.piece with
    | zero => simp
    | @homogeneous p x =>
      have hax : (a : A) • (x : M) ∈ M.grading.piece (q + p) :=
        SetLike.GradedSMul.smul_mem a.2 x.2
      rw [coindLiftLinear, DirectSum.homogeneousExtend_of_mem M.grading.piece _ hax,
        DirectSum.homogeneousExtend_of_mem M.grading.piece _ x.2]
      simp only [LinearMap.comp_apply, Submodule.coe_subtype, toCoindSummandLinear,
        LinearMap.coe_mk, AddHom.coe_mk, coindEndLinear_of_mem 𝒜 N a.2]
      exact congrArg (fun y ↦ DirectSum.lof k ℤ (fun _ ↦ CoindSummand k N) (q + p) ⟨y⟩)
        (f.hom.map_smul (a : A) ((x : M) : toModuleCat.obj M))
    | add m₁ m₂ hm₁ hm₂ => simp [smul_add, hm₁, hm₂]
  | add a₁ a₂ ha₁ ha₂ => simp [add_smul, ha₁, ha₂]

/-- Lift an ungraded `A`-linear morphism `toModuleCat.obj M ⟶ N` to a degree-zero graded morphism
`M ⟶ (coindFunctor 𝒜).obj N`. -/
def coindLift {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) : M ⟶ (coindFunctor 𝒜).obj N :=
  ofHom (M := M) (N := (coindFunctor 𝒜).obj N)
    { toFun := fun m ↦ by
        delta coindFunctor
        exact coindLiftLinear 𝒜 f m
      map_add' := fun x y ↦ by
        delta coindFunctor
        exact (coindLiftLinear 𝒜 f).map_add x y
      map_smul' := fun a m ↦ by
        delta coindFunctor
        exact coindLiftLinear_smul 𝒜 f a m }
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      delta coindFunctor
      rw [add_zero, coindObj_piece]
      -- Unfold the underlying linear map on `x` to `coindLiftLinear`.
      change coindLiftLinear 𝒜 f x ∈ _
      rw [coindLiftLinear, DirectSum.homogeneousExtend_of_mem M.grading.piece _ hx]
      exact _root_.DirectSum.lof_mem_summand p _)

/-- Composing `coindLift 𝒜 f` with the counit recovers `f`. -/
@[reassoc]
theorem toModuleCat_map_coindLift_comp_coindCounit {M : GradedModuleCat.{v} 𝒜}
    {N : ModuleCat.{v} A} (f : toModuleCat.obj M ⟶ N) :
    toModuleCat.map (coindLift 𝒜 f) ≫ coindCounit 𝒜 N = f := by
  have key : ∀ m : M, coindCounitAddHom k N (coindLiftLinear 𝒜 f m) = f.hom m := fun m ↦ by
    induction m using DirectSum.Decomposition.inductionOn M.grading.piece with
    | zero =>
      rw [map_zero, map_zero]
      exact f.hom.map_zero.symm
    | @homogeneous p x =>
      rw [coindLiftLinear, DirectSum.homogeneousExtend_of_mem M.grading.piece _ x.2]
      simp [coindCounitAddHom, coindSummandValAddHom, toCoindSummandLinear, DirectSum.lof_eq_of]
    | add m₁ m₂ hm₁ hm₂ =>
      rw [map_add, map_add, hm₁, hm₂]
      exact (f.hom.map_add m₁ m₂).symm
  delta coindLift coindCounit coindFunctor
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact key m

/-- The `simp`-normal form of `toModuleCat_map_coindLift_comp_coindCounit` after
`toModuleCat_map`. -/
@[simp]
theorem ofHom_hom_coindLift_comp_coindCounit {M : GradedModuleCat.{v} 𝒜}
    {N : ModuleCat.{v} A} (f : toModuleCat.obj M ⟶ N) :
    ModuleCat.ofHom (coindLift 𝒜 f).hom ≫ coindCounit 𝒜 N = f := by
  rw [← toModuleCat_map]
  exact toModuleCat_map_coindLift_comp_coindCounit 𝒜 f

private theorem coindLiftLinear_comp_coindCounitObj {M : GradedModuleCat.{v} 𝒜}
    {N : ModuleCat.{v} A} (g : M ⟶ coindObj 𝒜 N) (m : M) :
    coindLiftLinear 𝒜
        (toModuleCat.map g ≫
          ModuleCat.ofHom
            { toFun := fun z : coindObj 𝒜 N ↦ coindCounitAddHom k N z
              map_add' := fun x y ↦ (coindCounitAddHom k N).map_add x y
              map_smul' := fun a z ↦ coindCounitAddHom_endLinear 𝒜 N a z }) m =
      g.hom m := by
  induction m using DirectSum.Decomposition.inductionOn M.grading.piece with
  | zero =>
    rw [map_zero]
    exact g.hom.map_zero.symm
  | @homogeneous p x =>
    have hgx : g.hom x ∈ (coindObj 𝒜 N).grading.piece p := map_mem g x.2
    rw [coindObj_piece] at hgx
    obtain ⟨⟨y⟩, hy⟩ := _root_.DirectSum.mem_summand.mp hgx
    let gx : ⨁ _ : ℤ, CoindSummand k N := g.hom x
    have hgx_eq : gx = DirectSum.of (fun _ ↦ CoindSummand k N) p ⟨y⟩ := hy.symm
    rw [coindLiftLinear, DirectSum.homogeneousExtend_of_mem M.grading.piece _ x.2]
    -- Evaluate `toCoindSummandLinear` of the ungraded counit composite on `x`.
    change DirectSum.lof k ℤ (fun _ ↦ CoindSummand k N) p ⟨coindCounitAddHom k N gx⟩ = gx
    rw [hgx_eq, coindCounitAddHom, DirectSum.toAddMonoid_of, DirectSum.lof_eq_of]
    rfl
  | add m₁ m₂ hm₁ hm₂ =>
    rw [map_add, hm₁, hm₂]
    exact (g.hom.map_add m₁ m₂).symm

/-- Lifting the counit composite of a graded morphism `g : M ⟶ (coindFunctor 𝒜).obj N` recovers
`g`. -/
theorem coindLift_toModuleCat_map_comp_coindCounit {M : GradedModuleCat.{v} 𝒜}
    {N : ModuleCat.{v} A} (g : M ⟶ (coindFunctor 𝒜).obj N) :
    coindLift 𝒜 (toModuleCat.map g ≫ coindCounit 𝒜 N) = g := by
  delta coindLift coindCounit coindFunctor at g ⊢
  apply hom_ext
  apply LinearMap.ext
  intro m
  exact coindLiftLinear_comp_coindCounitObj 𝒜 g m

/-- Morphisms into `(coindFunctor 𝒜).obj N` are uniquely determined by their ungraded composites
with `coindCounit 𝒜 N`. -/
@[ext]
theorem coind_hom_ext {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    {f g : M ⟶ (coindFunctor 𝒜).obj N}
    (h : toModuleCat.map f ≫ coindCounit 𝒜 N = toModuleCat.map g ≫ coindCounit 𝒜 N) :
    f = g := by
  rw [← coindLift_toModuleCat_map_comp_coindCounit 𝒜 f, h,
    coindLift_toModuleCat_map_comp_coindCounit]

/-- Precomposing `coindLift 𝒜 f` with a graded morphism `u` lifts `toModuleCat.map u ≫ f`. -/
@[simp]
theorem comp_coindLift {M₁ M₂ : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (u : M₁ ⟶ M₂) (f : toModuleCat.obj M₂ ⟶ N) :
    u ≫ coindLift 𝒜 f = coindLift 𝒜 (toModuleCat.map u ≫ f) := by
  apply coind_hom_ext
  rw [Functor.map_comp, Category.assoc, toModuleCat_map_coindLift_comp_coindCounit,
    toModuleCat_map_coindLift_comp_coindCounit]

/-- Postcomposing `coindLift 𝒜 f` with `(coindFunctor 𝒜).map g` lifts `f ≫ g`. -/
@[simp]
theorem coindLift_comp_map {M : GradedModuleCat.{v} 𝒜} {N₁ N₂ : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N₁) (g : N₁ ⟶ N₂) :
    coindLift 𝒜 f ≫ (coindFunctor 𝒜).map g = coindLift 𝒜 (f ≫ g) := by
  apply coind_hom_ext
  rw [Functor.map_comp, Category.assoc, toModuleCat_map_coindFunctor_comp_coindCounit,
    ← Category.assoc, toModuleCat_map_coindLift_comp_coindCounit,
    toModuleCat_map_coindLift_comp_coindCounit]

/-- The additive universal property of `coindFunctor 𝒜`: graded morphisms into
`(coindFunctor 𝒜).obj N` correspond to ungraded `A`-linear morphisms into `N`. -/
def coindHomEquiv (M : GradedModuleCat.{v} 𝒜) (N : ModuleCat.{v} A) :
    (M ⟶ (coindFunctor 𝒜).obj N) ≃+ (toModuleCat.obj M ⟶ N) where
  toFun g := toModuleCat.map g ≫ coindCounit 𝒜 N
  invFun := coindLift 𝒜
  left_inv := coindLift_toModuleCat_map_comp_coindCounit 𝒜
  right_inv := toModuleCat_map_coindLift_comp_coindCounit 𝒜
  map_add' _ _ := by rw [Functor.map_add, Preadditive.add_comp]

/-- Applying `coindHomEquiv` composes the underlying ungraded map with `coindCounit`. -/
@[simp]
theorem coindHomEquiv_apply {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (g : M ⟶ (coindFunctor 𝒜).obj N) :
    coindHomEquiv 𝒜 M N g = toModuleCat.map g ≫ coindCounit 𝒜 N :=
  (rfl)

/-- The inverse of `coindHomEquiv` is `coindLift`. -/
@[simp]
theorem coindHomEquiv_symm_apply {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) :
    (coindHomEquiv 𝒜 M N).symm f = coindLift 𝒜 f :=
  (rfl)

/-- **Forgetting the grading is left adjoint to coinduction.** -/
def toModuleCatCoindAdj : toModuleCat.{v} (𝒜 := 𝒜) ⊣ coindFunctor.{v} 𝒜 :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦
        { toFun := coindLift 𝒜
          invFun := fun g ↦ toModuleCat.map g ≫ coindCounit 𝒜 N
          left_inv := toModuleCat_map_coindLift_comp_coindCounit 𝒜
          right_inv := coindLift_toModuleCat_map_comp_coindCounit 𝒜 }
      homEquiv_naturality_left_symm := fun _ _ ↦ by
        simp only [Equiv.coe_fn_symm_mk, Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := fun f g ↦
        (coindLift_comp_map 𝒜 f g).symm }

/-- The forward hom-equivalence of `toModuleCatCoindAdj` is `coindLift`. -/
@[simp]
theorem toModuleCatCoindAdj_homEquiv_apply {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) :
    (toModuleCatCoindAdj 𝒜).homEquiv M N f = coindLift 𝒜 f := by
  rw [toModuleCatCoindAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The inverse hom-equivalence of `toModuleCatCoindAdj` composes with `coindCounit`. -/
@[simp]
theorem toModuleCatCoindAdj_homEquiv_symm_apply {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (g : M ⟶ (coindFunctor 𝒜).obj N) :
    ((toModuleCatCoindAdj 𝒜).homEquiv M N).symm g = toModuleCat.map g ≫ coindCounit 𝒜 N := by
  rw [toModuleCatCoindAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The counit of `toModuleCatCoindAdj` at `N` is `coindCounit 𝒜 N`. -/
@[simp]
theorem toModuleCatCoindAdj_counit_app (N : ModuleCat.{v} A) :
    (toModuleCatCoindAdj 𝒜).counit.app N = coindCounit 𝒜 N := by
  rw [toModuleCatCoindAdj, Adjunction.mkOfHomEquiv_counit_app, Equiv.coe_fn_symm_mk,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Coinduction preserves injective objects, since `toModuleCat` preserves monomorphisms. -/
instance injective_coindFunctor_obj (N : ModuleCat.{v} A) [Injective N] :
    Injective ((coindFunctor 𝒜).obj N) :=
  Injective.injective_of_adjoint (toModuleCatCoindAdj 𝒜) N

/-- Every category of graded `𝒜`-modules in universe `max v uA` has enough injectives. -/
theorem enoughInjectives : EnoughInjectives (GradedModuleCat.{max v uA} 𝒜) :=
  letI := ModuleCat.enoughInjectives.{v, uA} A
  EnoughInjectives.of_adjunction (toModuleCatCoindAdj 𝒜)

/-- When `A` is small in universe `v` (in particular for `v = uA`), `GradedModuleCat.{v} 𝒜` has
enough injectives. -/
instance [Small.{v} A] : EnoughInjectives (GradedModuleCat.{v} 𝒜) :=
  EnoughInjectives.of_adjunction (toModuleCatCoindAdj 𝒜)

end TauCeti.GradedModuleCat
