/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Local coefficients from covering spaces

A covering transports its fibre along paths by monodromy. Applying the free-module construction
to this set-valued local system gives a module-valued local coefficient system whose fibres are
the finitely supported formal sums of sheets. This is the permutation local system used to
describe singular transfer for finite covers, including covers that are not regular.

The construction does not require finite fibres: finiteness is needed only by later transfer
formulas, not to define the local system. The basis-vector formula records the sheet-level
transport explicitly, so a later chain-level transfer can use the same path-lifting data.

For a ring `R` in the universe of the spaces, the permutation local system is related to the
constant system with fibre `R` by two morphisms of local systems. The augmentation
`IsCoveringMap.permutationLocalSystemAugmentation` adds up the coefficients of all sheets, and, when
the fibres are finite, the transfer `IsCoveringMap.permutationLocalSystemTransfer` sends `r` to the
sum of all sheets with coefficient `r`. On singular chains they induce the projection and the
transfer of the covering (`TauCeti.AlgebraicTopology.Singular.Transfer.PermutationLocalSystem`).

A continuous map `σ : E → E` over the base commutes with monodromy, so moving each sheet by `σ`
is an endomorphism of the permutation local system
(`IsCoveringMap.permutationLocalSystemFiberMap`). On singular chains it induces `σ_*`. Likewise
monodromy follows a continuous section `s` of `p`, so `r ↦ r • s x` is a morphism from the
constant system (`IsCoveringMap.permutationLocalSystemSection`), which induces `s_*`.

The local-system viewpoint follows Hatcher, *Algebraic Topology*, Section 3.H; the covering
monodromy is Mathlib's `IsCoveringMap.monodromyFunctor`.
-/

public section

open CategoryTheory

universe u v w

namespace IsCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B}

/-- The permutation local coefficient system of a covering map, with fibre the free `R`-module
on the sheet over each point. Its transport maps are the linear extensions of path lifting. -/
@[expose] noncomputable def permutationLocalSystem (hp : IsCoveringMap p) (R : Type v)
    [Ring R] : TauCeti.LocalCoefficientSystem R B where
  obj x := ModuleCat.of R ((p ⁻¹' {x.as}) →₀ R)
  map {x y} γ := ModuleCat.ofHom <|
    Finsupp.lmapDomain R R (hp.monodromy γ)
  map_id x := by
    have hmon : hp.monodromy (𝟙 x) = id := by
      -- The groupoid identity is represented by the reflexive path class.
      rw [show (𝟙 x : x ⟶ x) = Path.Homotopic.Quotient.refl x.as from rfl,
        hp.monodromy_refl]
    ext f e
    simp [hmon]
  map_comp γ δ := by
    have hmon : hp.monodromy (γ ≫ δ) = hp.monodromy δ ∘ hp.monodromy γ :=
      funext fun e => hp.monodromy_trans_apply γ δ e
    ext f e
    simp [hmon]

/-- The fibre of the permutation local coefficient system over `x` is the free module on the
sheet over `x`. -/
theorem permutationLocalSystem_obj (hp : IsCoveringMap p) (R : Type v) [Ring R]
    (x : FundamentalGroupoid B) :
    (hp.permutationLocalSystem R).obj x =
      ModuleCat.of R ((p ⁻¹' {x.as}) →₀ R) :=
  rfl

/-- Evaluating transport in the permutation local system is the linear extension of monodromy. -/
@[simp]
theorem permutationLocalSystem_map_apply (hp : IsCoveringMap p) (R : Type v) [Ring R]
    {x y : FundamentalGroupoid B} (γ : x ⟶ y) (f : (p ⁻¹' {x.as}) →₀ R) :
    ((hp.permutationLocalSystem R).map γ).hom f =
      Finsupp.lmapDomain R R (hp.monodromy γ) f :=
  rfl

/-- Transport sends each basis vector to the basis vector of the lifted endpoint. -/
theorem permutationLocalSystem_map_single (hp : IsCoveringMap p) (R : Type v) [Ring R]
    {x y : FundamentalGroupoid B} (γ : x ⟶ y) (e : p ⁻¹' {x.as}) (r : R) :
    ((hp.permutationLocalSystem R).map γ).hom (Finsupp.single e r) =
      Finsupp.single (hp.monodromy γ e) r := by
  rw [permutationLocalSystem_map_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

section Transfer

variable (hp : IsCoveringMap p) (R : Type u) [Ring R]

/-- The inclusion of the coefficients at a single sheet `e` into the fibre of the permutation local
coefficient system over `x`, that is `r ↦ Finsupp.single e r`. -/
noncomputable def permutationLocalSystemSingle (x : FundamentalGroupoid B) (e : p ⁻¹' {x.as}) :
    ModuleCat.of R R ⟶ (hp.permutationLocalSystem R).obj x :=
  ModuleCat.ofHom (Finsupp.lsingle e)

/-- The inclusion of the coefficients at a sheet `e` sends `r` to `Finsupp.single e r`. -/
@[simp]
theorem permutationLocalSystemSingle_hom_apply (x : FundamentalGroupoid B) (e : p ⁻¹' {x.as})
    (r : R) :
    (hp.permutationLocalSystemSingle R x e).hom r = Finsupp.single e r :=
  (rfl)

/-- Two morphisms out of a fibre of the permutation local system agree as soon as they agree on
the coefficients at every sheet. -/
@[ext]
theorem permutationLocalSystem_hom_ext {x : FundamentalGroupoid B} {M : ModuleCat.{u} R}
    {f g : (hp.permutationLocalSystem R).obj x ⟶ M}
    (h : ∀ e, hp.permutationLocalSystemSingle R x e ≫ f =
      hp.permutationLocalSystemSingle R x e ≫ g) :
    f = g :=
  ModuleCat.hom_ext (Finsupp.lhom_ext' fun e ↦ ModuleCat.hom_ext_iff.mp (h e))

/-- Transport in the permutation local system carries the coefficients at a sheet to the
coefficients at the lifted endpoint of that sheet. -/
@[reassoc (attr := simp)]
theorem permutationLocalSystemSingle_map {x y : FundamentalGroupoid B} (γ : x ⟶ y)
    (e : p ⁻¹' {x.as}) :
    hp.permutationLocalSystemSingle R x e ≫ (hp.permutationLocalSystem R).map γ =
      hp.permutationLocalSystemSingle R y (hp.monodromy γ e) := by
  ext : 1
  exact LinearMap.ext_ring (hp.permutationLocalSystem_map_single R γ e 1)

/-- The augmentation of the permutation local coefficient system: on the fibre over each point it
sends a formal sum of sheets to the sum of its coefficients. It commutes with transport because
monodromy only permutes the sheets. -/
noncomputable def permutationLocalSystemAugmentation :
    hp.permutationLocalSystem R ⟶
      (TauCeti.LocalCoefficientSystem.constantFunctor B).obj (ModuleCat.of R R) where
  app x := ModuleCat.ofHom (Finsupp.linearCombination R fun _ ↦ (1 : R))
  naturality x y γ := by
    dsimp only [permutationLocalSystem, TauCeti.LocalCoefficientSystem.constantFunctor,
      Functor.const_obj_map, Functor.const_obj_obj]
    rw [Category.comp_id, ← ModuleCat.ofHom_comp]
    congr 1
    ext e
    simp

/-- The augmentation sends a formal sum of sheets to the sum of its coefficients. -/
theorem permutationLocalSystemAugmentation_app_apply (x : FundamentalGroupoid B)
    (f : (p ⁻¹' {x.as}) →₀ R) :
    ((hp.permutationLocalSystemAugmentation R).app x).hom f = f.sum fun _ r ↦ r := by
  -- The codomain is the fibre `((constantFunctor B).obj (ModuleCat.of R R)).obj x`, which is `R`
  -- only after unfolding the constant functor, so no `R`-module instance or `Finsupp` lemma applies
  -- to the component as stated. `change` restates it as the linear combination it is defined as.
  change Finsupp.linearCombination R (fun _ ↦ (1 : R)) f = _
  simp [Finsupp.linearCombination_apply]

/-- Over a finite fibre, the augmentation sends a formal sum of sheets to the sum of its
coefficients over all the sheets. -/
theorem permutationLocalSystemAugmentation_app_apply_eq_sum (x : FundamentalGroupoid B)
    [Fintype (p ⁻¹' {x.as})] (f : (p ⁻¹' {x.as}) →₀ R) :
    ((hp.permutationLocalSystemAugmentation R).app x).hom f = ∑ e, f e :=
  (hp.permutationLocalSystemAugmentation_app_apply R x f).trans
    (Finsupp.sum_fintype _ _ fun _ ↦ rfl)

/-- The augmentation of the permutation local system is the identity on the coefficients at each
sheet. -/
@[reassoc (attr := simp)]
theorem permutationLocalSystemSingle_augmentation_app (x : FundamentalGroupoid B)
    (e : p ⁻¹' {x.as}) :
    hp.permutationLocalSystemSingle R x e ≫ (hp.permutationLocalSystemAugmentation R).app x =
      𝟙 _ := by
  ext : 1
  exact LinearMap.ext_ring (Finsupp.linearCombination_single R 1 e |>.trans (mul_one (1 : R)))

/-- The transfer of the permutation local coefficient system of a covering with finite fibres: on
the fibre over each point it sends `r` to the formal sum of all sheets with coefficient `r`. It
commutes with transport because monodromy permutes the sheets bijectively. -/
noncomputable def permutationLocalSystemTransfer (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) :
    (TauCeti.LocalCoefficientSystem.constantFunctor B).obj (ModuleCat.of R R) ⟶
      hp.permutationLocalSystem R where
  app x := haveI := hfin x.as
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (Finsupp.equivFunOnFinite.symm 1))
  naturality x y γ := by
    have := hfin x.as
    have := hfin y.as
    dsimp only [permutationLocalSystem, TauCeti.LocalCoefficientSystem.constantFunctor,
      Functor.const_obj_map, Functor.const_obj_obj]
    rw [Category.id_comp, ← ModuleCat.ofHom_comp]
    congr 1
    refine LinearMap.ext_ring (Finsupp.ext fun e ↦ ?_)
    obtain ⟨e, rfl⟩ := (hp.monodromy_bijective γ).2 e
    simp [Finsupp.mapDomain_apply_of_injective (hp.monodromy_bijective γ).1]

/-- The transfer of the permutation local system is the sum, over all sheets, of the inclusions of
the coefficients at that sheet. -/
theorem permutationLocalSystemTransfer_app (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))
    (x : FundamentalGroupoid B) [Fintype (p ⁻¹' {x.as})] :
    (hp.permutationLocalSystemTransfer R hfin).app x =
      ∑ e, hp.permutationLocalSystemSingle R x e := by
  -- The component is by definition `r ↦ r • Finsupp.equivFunOnFinite.symm 1`, but its source is
  -- the fibre of the constant system, which `ModuleCat.hom_ofHom` does not see through.
  change ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (Finsupp.equivFunOnFinite.symm 1)) =
    ∑ e, ModuleCat.ofHom (Finsupp.lsingle e)
  ext : 1
  refine LinearMap.ext_ring ?_
  simp [Finsupp.equivFunOnFinite_symm_eq_sum]

/-- The transfer of the permutation local system has coefficient `r` at every sheet. -/
theorem permutationLocalSystemTransfer_app_hom_apply_apply (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))
    (x : FundamentalGroupoid B) (r : R) (e : p ⁻¹' {x.as}) :
    DFunLike.coe (F := (p ⁻¹' {x.as}) →₀ R)
      (((hp.permutationLocalSystemTransfer R hfin).app x).hom r) e = r := by
  have := hfin x.as
  -- The fibres of the constant and permutation systems are `R` and formal sums of sheets only
  -- after unfolding their definitions, so `change` states the component as the multiple of the
  -- formal sum of all sheets that it is defined as.
  change (r • Finsupp.equivFunOnFinite.symm (1 : p ⁻¹' {x.as} → R)) e = r
  simp

end Transfer

section Section

variable (hp : IsCoveringMap p) (R : Type u) [Ring R] (s : C(B, E)) (hs : ∀ b, s b ∈ p ⁻¹' {b})

/-- The morphism from the constant system to the permutation local system given by a continuous
section `s` of `p`: on the fibre over `x` it sends `r` to the formal sum `r • s x`. It commutes
with transport because monodromy follows continuous sections. -/
noncomputable def permutationLocalSystemSection :
    (TauCeti.LocalCoefficientSystem.constantFunctor B).obj (ModuleCat.of R R) ⟶
      hp.permutationLocalSystem R where
  app x := hp.permutationLocalSystemSingle R x ⟨s x.as, hs x.as⟩
  naturality x y γ := by
    dsimp only [TauCeti.LocalCoefficientSystem.constantFunctor, Functor.const_obj_map,
      Functor.const_obj_obj]
    rw [Category.id_comp, permutationLocalSystemSingle_map]
    exact congrArg _ (hp.monodromy_section s.continuous hs γ).symm

/-- The morphism given by a section `s` is, over `x`, the inclusion of the coefficients at the
sheet `s x`. -/
@[simp]
theorem permutationLocalSystemSection_app (x : FundamentalGroupoid B) :
    (hp.permutationLocalSystemSection R s hs).app x =
      hp.permutationLocalSystemSingle R x ⟨s x.as, hs x.as⟩ :=
  (rfl)

end Section

section FiberMap

variable (hp : IsCoveringMap p) (R : Type u) [Ring R] (σ : C(E, E)) (hσ : ⇑p ∘ ⇑σ = ⇑p)

/-- The endomorphism of the permutation local system of `p` moving each sheet by a map `σ` over
the base: on the fibre over `x` it is the linear extension of `σ` restricted to that fibre. It
commutes with transport because `σ` commutes with monodromy. -/
noncomputable def permutationLocalSystemFiberMap :
    hp.permutationLocalSystem R ⟶ hp.permutationLocalSystem R where
  app x := ModuleCat.ofHom (Finsupp.lmapDomain R R (Function.fiberMap σ hσ x.as))
  naturality x y γ := by
    dsimp only [permutationLocalSystem]
    rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
    congr 1
    refine Finsupp.lhom_ext' fun e ↦ LinearMap.ext_ring ?_
    simp [hp.fiberMap_monodromy hp σ hσ]

/-- The endomorphism moving the sheets by `σ` is the linear extension of `σ` on each fibre. -/
@[simp]
theorem permutationLocalSystemFiberMap_app_apply (x : FundamentalGroupoid B)
    (f : (p ⁻¹' {x.as}) →₀ R) :
    ((hp.permutationLocalSystemFiberMap R σ hσ).app x).hom f =
      Finsupp.mapDomain (Function.fiberMap σ hσ x.as) f :=
  (rfl)

/-- The endomorphism moving the sheets by `σ` sends the coefficients at a sheet `e` to the
coefficients at `σ e`. -/
@[reassoc (attr := simp)]
theorem permutationLocalSystemSingle_fiberMap_app (x : FundamentalGroupoid B)
    (e : p ⁻¹' {x.as}) :
    hp.permutationLocalSystemSingle R x e ≫ (hp.permutationLocalSystemFiberMap R σ hσ).app x =
      hp.permutationLocalSystemSingle R x (Function.fiberMap σ hσ x.as e) := by
  ext : 1
  refine LinearMap.ext_ring ?_
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, permutationLocalSystemSingle_hom_apply,
    permutationLocalSystemSingle_hom_apply, permutationLocalSystemFiberMap_app_apply,
    Finsupp.mapDomain_single]

end FiberMap

end IsCoveringMap
