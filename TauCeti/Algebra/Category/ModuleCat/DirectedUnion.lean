/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import TauCeti.LinearAlgebra.Submodule.DirectedUnion
public import TauCeti.LinearAlgebra.TensorProduct.Tower

/-!
# Directed unions as colimits of modules

A monotone family of submodules over a directed preorder defines a diagram in `ModuleCat`, with
the submodule inclusions as transition maps. If its supremum is a submodule `T`, the inclusions
into `T` exhibit `ModuleCat.of R T` as the colimit of this diagram.

The universal map is the linear map `Submodule.iSupLift` glued from the legs of an
arbitrary cocone.

Dually, let a commutative ring `R` be the union of an increasing sequence of subrings
`S₀ ⊆ S₁ ⊆ ⋯`. Every `R`-module `M` is the colimit of its base changes `R ⊗[Sₙ] M`, with
transition maps `r ⊗ m ↦ r ⊗ m` and legs `r ⊗ m ↦ r • m`: each element of `R` already lies in
some `Sₙ`, where it can be moved across the tensor sign.

## Main declarations

* `TauCeti.ModuleCat.submoduleFunctor`: the diagram associated to a monotone family of submodules.
* `TauCeti.ModuleCat.submoduleCocone`: the inclusion cocone into the supremum submodule.
* `TauCeti.ModuleCat.submoduleCoconeIsColimit`: the inclusion cocone is a colimit.
* `TauCeti.ModuleCat.tensorSubringFunctor`: the sequence `n ↦ R ⊗[S n] M` of base changes of an
  `R`-module along an increasing sequence of subrings.
* `TauCeti.ModuleCat.tensorSubringCocone`: the cocone over it with point `M`.
* `TauCeti.ModuleCat.isColimitTensorSubringCocone`: this cocone is a colimit when the subrings
  exhaust `R`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u v x

namespace ModuleCat

variable {R : Type u} {M : Type v} {ι : Type x}
variable [Ring R] [AddCommGroup M] [Module R M]
variable [Preorder ι]

private theorem inclusion_hom_ext {A B : Submodule R M}
    (f g : ModuleCat.of R A ⟶ ModuleCat.of R B)
    (h : ∀ m, ((f m : B) : M) = g m) : f = g := by
  apply ModuleCat.hom_ext
  ext m
  exact h m

/-- A monotone family of submodules, regarded as a diagram in `ModuleCat` whose maps are the
canonical inclusions. -/
noncomputable def submoduleFunctor (K : ι → Submodule R M) (hK : Monotone K) :
    CategoryTheory.Functor ι (ModuleCat.{v} R) where
  obj i := ModuleCat.of R (K i)
  map f := ModuleCat.ofHom (Submodule.inclusion (hK (leOfHom f)))
  map_id i := by
    apply inclusion_hom_ext
    intro m
    rfl
  map_comp f g := by
    apply inclusion_hom_ext
    intro m
    rfl

/-- The object at an index of the submodule diagram is the corresponding submodule. -/
@[simp]
theorem submoduleFunctor_obj (K : ι → Submodule R M) (hK : Monotone K) (i : ι) :
    (submoduleFunctor K hK).obj i = ModuleCat.of R (K i) :=
  by rw [submoduleFunctor]

/-- A map in the submodule diagram is the canonical inclusion. -/
@[simp]
theorem submoduleFunctor_map (K : ι → Submodule R M) (hK : Monotone K)
    {i j : ι} (f : i ⟶ j) :
    eqToHom (submoduleFunctor_obj K hK i).symm ≫
        (submoduleFunctor K hK).map f ≫
      eqToHom (submoduleFunctor_obj K hK j) =
      ModuleCat.ofHom (Submodule.inclusion (hK (leOfHom f))) :=
  by
    unfold submoduleFunctor
    simp

/-- The cocone from a monotone family of submodules to a submodule equal to their supremum. -/
noncomputable def submoduleCocone (K : ι → Submodule R M) (hK : Monotone K)
    (T : Submodule R M) (hT : ⨆ i, K i = T) : Cocone (submoduleFunctor K hK) :=
  Cocone.mk (ModuleCat.of R T)
    { app := fun i ↦ ModuleCat.ofHom (Submodule.inclusion ((le_iSup K i).trans hT.le))
      naturality := fun _ _ _ ↦ by
        apply inclusion_hom_ext
        intro m
        rfl }

/-- The point of the directed-submodule cocone is the module carried by the supremum. -/
@[simp]
theorem submoduleCocone_pt (K : ι → Submodule R M) (hK : Monotone K)
    (T : Submodule R M) (hT : ⨆ i, K i = T) :
    (submoduleCocone K hK T hT).pt = ModuleCat.of R T :=
  by rw [submoduleCocone]

/-- A leg of the directed-submodule cocone is the corresponding submodule inclusion. -/
@[simp]
theorem submoduleCocone_ι_app (K : ι → Submodule R M) (hK : Monotone K)
    (T : Submodule R M) (hT : ⨆ i, K i = T) (i : ι) :
    eqToHom (submoduleFunctor_obj K hK i).symm ≫
        (submoduleCocone K hK T hT).ι.app i ≫
      eqToHom (submoduleCocone_pt K hK T hT) =
      ModuleCat.ofHom (Submodule.inclusion ((le_iSup K i).trans hT.le)) :=
  by
    unfold submoduleCocone submoduleFunctor
    simp

private noncomputable abbrev coconeLinearMap (K : ι → Submodule R M) (hK : Monotone K)
    (s : Cocone (submoduleFunctor K hK)) (i : ι) : K i →ₗ[R] s.pt :=
  (s.ι.app i).hom

private theorem submoduleFunctor_ι_app_eq_comp_inclusion [IsDirectedOrder ι]
    (K : ι → Submodule R M) (hK : Monotone K) (s : Cocone (submoduleFunctor K hK))
    (i j : ι) (hij : K i ≤ K j) :
    coconeLinearMap K hK s i =
      (coconeLinearMap K hK s j).comp (Submodule.inclusion hij) := by
  apply LinearMap.ext
  intro m
  have h_app {a b : ι} (hab : a ≤ b) (x : K a) :
      coconeLinearMap K hK s b (Submodule.inclusion (hK hab) x) =
        coconeLinearMap K hK s a x := by
    have h : (coconeLinearMap K hK s b).comp (Submodule.inclusion (hK hab)) =
        coconeLinearMap K hK s a := by
      have hw := congrArg ModuleCat.Hom.hom (s.w (homOfLE hab))
      simp only [submoduleFunctor, ModuleCat.hom_comp,
        ConcreteCategory.hom_ofHom] at hw
      exact hw
    exact LinearMap.congr_fun h x
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  calc
    coconeLinearMap K hK s i m =
        coconeLinearMap K hK s k (Submodule.inclusion (hK hik) m) := (h_app hik m).symm
    _ = coconeLinearMap K hK s k
        (Submodule.inclusion (hK hjk) (Submodule.inclusion hij m)) := by rfl
    _ = coconeLinearMap K hK s j (Submodule.inclusion hij m) := h_app hjk _

/-- A submodule equal to the supremum of a monotone family over a directed preorder is the
colimit of that family in `ModuleCat`. -/
noncomputable def submoduleCoconeIsColimit [IsDirectedOrder ι]
    (K : ι → Submodule R M) (hK : Monotone K)
    (T : Submodule R M) (hT : ⨆ i, K i = T) : IsColimit (submoduleCocone K hK T hT) where
  desc s := ModuleCat.ofHom (Submodule.iSupLift K hK.directed_le
    (coconeLinearMap K hK s) (submoduleFunctor_ι_app_eq_comp_inclusion K hK s)
    T hT.ge)
  fac s i := by
    apply ModuleCat.hom_ext
    -- `ModuleCat.hom_ext` reduces the categorical equality to equality of bundled linear maps;
    -- exposing that representation lets the linear universal-property lemma apply directly.
    change (Submodule.iSupLift K hK.directed_le (coconeLinearMap K hK s)
      (submoduleFunctor_ι_app_eq_comp_inclusion K hK s) T hT.ge).comp
        (Submodule.inclusion ((le_iSup K i).trans hT.le)) = coconeLinearMap K hK s i
    exact Submodule.iSupLift_comp_inclusion
      (dir := hK.directed_le)
      (hf := submoduleFunctor_ι_app_eq_comp_inclusion K hK s)
      ((le_iSup K i).trans hT.le)
  uniq s g hg := by
    apply ModuleCat.hom_ext
    apply Submodule.iSupLift_unique
      (dir := hK.directed_le)
      (hf := submoduleFunctor_ι_app_eq_comp_inclusion K hK s)
    intro i m _
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (hg i)) m

end ModuleCat

namespace ModuleCat

section Subring

variable {R : Type u} [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- For subrings `A ≤ B` of `R`, the map `R ⊗[A] M → R ⊗[B] M`, `r ⊗ m ↦ r ⊗ m`. -/
noncomputable def tensorSubringMap {A B : Subring R} (h : A ≤ B) :
    R ⊗[A] M →ₗ[R] R ⊗[B] M :=
  have : CompatibleSMul B A R M := ⟨fun a r m ↦ by
    simpa [Subring.smul_def] using smul_tmul (⟨a, h a.2⟩ : B) r m⟩
  mapOfCompatibleSMul B A R R M

@[simp]
theorem tensorSubringMap_tmul {A B : Subring R} (h : A ≤ B) (r : R) (m : M) :
    tensorSubringMap M h (r ⊗ₜ m) = r ⊗ₜ m :=
  (rfl)

variable {S : ℕ → Subring R} (hS : Monotone S)

/-- The sequence `n ↦ R ⊗[S n] M` of base changes of `M` along an increasing sequence of
subrings, with transition maps `tensorSubringMap`. -/
noncomputable def tensorSubringFunctor : ℕ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (R ⊗[S n] M)
  map f := ModuleCat.ofHom (tensorSubringMap M (hS f.le))
  map_id n := by
    ext : 1
    exact AlgebraTensorModule.ext fun r m ↦ by simp
  map_comp f g := by
    ext : 1
    exact AlgebraTensorModule.ext fun r m ↦ by simp

/-- The object at stage `n` of `tensorSubringFunctor M hS` is the base change `R ⊗[S n] M`. -/
@[simp]
theorem tensorSubringFunctor_obj (n : ℕ) :
    (tensorSubringFunctor M hS).obj n = ModuleCat.of R (R ⊗[S n] M) :=
  by rw [tensorSubringFunctor]

/-- A transition map of `tensorSubringFunctor M hS` is `tensorSubringMap`. -/
@[simp]
theorem tensorSubringFunctor_map {i j : ℕ} (f : i ⟶ j) :
    eqToHom (tensorSubringFunctor_obj M hS i).symm ≫
        (tensorSubringFunctor M hS).map f ≫
      eqToHom (tensorSubringFunctor_obj M hS j) =
      ModuleCat.ofHom (tensorSubringMap M (hS f.le)) :=
  by
    unfold tensorSubringFunctor
    simp

/-- The cocone over `tensorSubringFunctor M hS` with point `M` and legs `r ⊗ m ↦ r • m`. -/
noncomputable def tensorSubringCocone : Cocone (tensorSubringFunctor M hS) where
  pt := ModuleCat.of R M
  ι :=
    { app n := ModuleCat.ofHom (LinearMap.liftBaseChange R (LinearMap.id : M →ₗ[S n] M))
      naturality i j f := by
        ext : 1
        refine AlgebraTensorModule.ext fun r m ↦ ?_
        simp [tensorSubringFunctor] }

/-- The point of `tensorSubringCocone M hS` is `M`. -/
@[simp]
theorem tensorSubringCocone_pt : (tensorSubringCocone M hS).pt = ModuleCat.of R M :=
  by rw [tensorSubringCocone]

/-- The leg at stage `n` of `tensorSubringCocone M hS` is `LinearMap.liftBaseChange` of the
identity of `M`. -/
@[simp]
theorem tensorSubringCocone_ι_app (n : ℕ) :
    eqToHom (tensorSubringFunctor_obj M hS n).symm ≫
        (tensorSubringCocone M hS).ι.app n ≫
      eqToHom (tensorSubringCocone_pt M hS) =
      ModuleCat.ofHom (LinearMap.liftBaseChange R (LinearMap.id : M →ₗ[S n] M)) :=
  by
    unfold tensorSubringCocone tensorSubringFunctor
    simp

/-- The legs of `tensorSubringCocone M hS` send `r ⊗ m` to `r • m`. -/
private theorem tensorSubringCocone_ι_app_tmul (n : ℕ) (r : R) (m : M) :
    ((tensorSubringCocone M hS).ι.app n).hom (r ⊗ₜ[S n] m : R ⊗[S n] M) = (r • m : M) := by
  -- The point `(tensorSubringCocone M hS).pt` is only definitionally `ModuleCat.of R M`, so
  -- `ModuleCat.hom_ofHom` cannot fire under `rw` or `simp`; `change` exposes the underlying map.
  change LinearMap.liftBaseChange R (LinearMap.id : M →ₗ[S n] M) (r ⊗ₜ m) = r • m
  simp

variable {M hS}

/-- The leg at stage `n` of a cocone over `tensorSubringFunctor M hS`, as an `R`-linear map out of
`R ⊗[S n] M`. -/
private noncomputable abbrev tensorSubringLeg (s : Cocone (tensorSubringFunctor M hS)) (n : ℕ) :
    R ⊗[S n] M →ₗ[R] s.pt :=
  (s.ι.app n).hom

/-- The legs of a cocone over `tensorSubringFunctor M hS` agree on `1 ⊗ m` at every stage. -/
private theorem tensorSubringLeg_one_tmul (s : Cocone (tensorSubringFunctor M hS)) (n : ℕ)
    (m : M) : tensorSubringLeg s n ((1 : R) ⊗ₜ m) = tensorSubringLeg s 0 ((1 : R) ⊗ₜ m) :=
  congr($(s.w (homOfLE (Nat.zero_le n))).hom ((1 : R) ⊗ₜ[S 0] m : R ⊗[S 0] M))

/-- `m ↦ tensorSubringLeg s 0 (1 ⊗ m)` is `R`-linear when the `S n` exhaust `R`: for `r ∈ S k`,
the element `1 ⊗ r • m` is `r • (1 ⊗ m)` at stage `k`. -/
private theorem tensorSubringLeg_one_tmul_smul (htop : ∀ r, ∃ n, r ∈ S n)
    (s : Cocone (tensorSubringFunctor M hS)) (r : R) (m : M) :
    tensorSubringLeg s 0 ((1 : R) ⊗ₜ (r • m)) = r • tensorSubringLeg s 0 ((1 : R) ⊗ₜ m) := by
  obtain ⟨k, hk⟩ := htop r
  rw [← tensorSubringLeg_one_tmul s k, ← tensorSubringLeg_one_tmul s k,
    ← tmul_eq_one_tmul_smul_of_mem hk, tmul_eq_smul_one_tmul, map_smul]

/-- When the subrings `S n` exhaust `R`, the module `M` is the colimit of the base changes
`R ⊗[S n] M`. -/
noncomputable def isColimitTensorSubringCocone (htop : ∀ r, ∃ n, r ∈ S n) :
    IsColimit (tensorSubringCocone M hS) where
  desc s := ModuleCat.ofHom
    { toFun m := tensorSubringLeg s 0 ((1 : R) ⊗ₜ m)
      map_add' m m' := by simp [tmul_add]
      map_smul' := tensorSubringLeg_one_tmul_smul htop s }
  fac s n := by
    ext : 1
    refine AlgebraTensorModule.ext fun r m ↦ ?_
    have h : tensorSubringLeg s n (r ⊗ₜ m) = r • tensorSubringLeg s 0 ((1 : R) ⊗ₜ m) := by
      rw [← tensorSubringLeg_one_tmul s n, tmul_eq_smul_one_tmul, map_smul]
    -- The composite is not type-correct at reducible transparency, since the cocone point is
    -- only definitionally `ModuleCat.of R M`; `rw [ModuleCat.hom_comp]` and `dsimp` fail on it,
    -- so `change` evaluates the composite and the explicit `desc` map directly.
    change tensorSubringLeg s 0 ((1 : R) ⊗ₜ ((tensorSubringCocone M hS).ι.app n).hom (r ⊗ₜ m)) =
      tensorSubringLeg s n (r ⊗ₜ m)
    rw [tensorSubringCocone_ι_app_tmul, tensorSubringLeg_one_tmul_smul htop s r m, h]
  uniq s g hg := by
    ext : 1
    refine LinearMap.ext fun (m : M) ↦ ?_
    calc g.hom m = g.hom (((tensorSubringCocone M hS).ι.app 0).hom
          ((1 : R) ⊗ₜ[S 0] m : R ⊗[S 0] M)) := by
          rw [tensorSubringCocone_ι_app_tmul, one_smul]
      _ = (s.ι.app 0).hom ((1 : R) ⊗ₜ[S 0] m : R ⊗[S 0] M) :=
          congr($(hg 0).hom ((1 : R) ⊗ₜ[S 0] m : R ⊗[S 0] M))

/-- The map out of `M` induced by a cocone `s` over `tensorSubringFunctor M hS` sends `m` to the
image of `1 ⊗ m` under any leg of `s`. -/
theorem isColimitTensorSubringCocone_desc_apply (htop : ∀ r, ∃ n, r ∈ S n)
    (s : Cocone (tensorSubringFunctor M hS)) (n : ℕ) (m : M) :
    (eqToHom (tensorSubringCocone_pt M hS).symm ≫ (isColimitTensorSubringCocone htop).desc s).hom
        m =
      (eqToHom (tensorSubringFunctor_obj M hS n).symm ≫ s.ι.app n).hom ((1 : R) ⊗ₜ m) :=
  (tensorSubringLeg_one_tmul s n m).symm

end Subring

end ModuleCat

end TauCeti
