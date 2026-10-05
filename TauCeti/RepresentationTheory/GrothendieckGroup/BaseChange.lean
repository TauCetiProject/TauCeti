/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.GrothendieckGroup.FDRep

/-!
# Base change on the Grothendieck ring of finite-dimensional representations

Let `k` and `k'` be fields with `k'` a `k`-algebra, and let `G` be a monoid. Extending the
scalars of a finite-dimensional representation, `V ↦ k' ⊗[k] V` with `g` acting by `1 ⊗ V.ρ g`
(`Representation.baseChange`), is a functor `TauCeti.baseChangeFDRep : FDRep k G ⥤ FDRep k' G`.
It is additive, because base change is additive on linear maps, and it is **exact**, because
`k'` is flat over `k`: a short exact sequence of representations stays short exact after
tensoring, which is `Module.Flat.lTensor_exact` together with the preservation of injectivity
and of surjectivity, read through the faithful exact forgetful functor to `k'`-modules.

So base change descends to the exact Grothendieck group, and because it carries the tensor unit
`k` to `k' ⊗[k] k ≅ k'` and a tensor product to a tensor product
(`TensorProduct.AlgebraTensorModule.distribBaseChange`), the descended map is a homomorphism of
rings

```text
baseChangeK0 k' : G₀(k[G]) →+* G₀(k'[G]),   [V] ↦ [k' ⊗[k] V].
```

This is the base-change homomorphism of the Grothendieck rings `R_k(G) → R_{k'}(G)` of Serre,
Part III. It is the comparison along which an identity in `G₀` proved over one field is
transported to an extension of that field -- in particular to a splitting field. It is the
identity for `k' = k`, transitive along a tower, and it takes the class of a permutation
representation `k[X]` to the class of `k'[X]`.

The functor is built here rather than beside `Representation.baseChange` because its purpose is
to feed the Grothendieck-ring homomorphism; the ring map asks for no monoidal-functor structure
on it, only for the two comparison isomorphisms recorded below.

## Main definitions

* `TauCeti.fdRepIsoOfEquivariant`: an isomorphism in `FDRep` from an equivariant linear
  equivalence.
* `TauCeti.baseChangeFDRepHom`: base change of an equivariant map.
* `TauCeti.baseChangeFDRep`: scalar extension as a functor `FDRep k G ⥤ FDRep k' G`.
* `TauCeti.baseChangeFDRepUnitIso` and `TauCeti.baseChangeFDRepTensorIso`: the comparison
  isomorphisms `k' ⊗[k] k ≅ k'` and `k' ⊗[k] (V ⊗ W) ≅ (k' ⊗[k] V) ⊗ (k' ⊗[k] W)`.
* `TauCeti.baseChangeK0`: base change on the exact Grothendieck ring, as a ring homomorphism.

## Main results

* `TauCeti.shortExact_map_baseChangeFDRep` and `TauCeti.isConflationExact_baseChangeFDRep`:
  **base change is exact.**
* `TauCeti.baseChangeK0_of`: the class of a representation goes to the class of its scalar
  extension.
* `TauCeti.baseChangeK0_id` and `TauCeti.baseChangeK0_comp`: base change along the identity is
  the identity, and base change along a tower is the composite.
* `TauCeti.baseChangeK0_of_ofMulAction`: base change preserves permutation classes.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part III,
  §14.1 and §15.5, for `R_k(G)` and its behaviour under extension of the base field.
-/

@[expose] public section

open CategoryTheory MonoidalCategory TensorProduct

namespace TauCeti

universe u v

variable {k : Type u} (k' : Type u) [Field k] [Field k'] [Algebra k k'] {G : Type v} [Monoid G]

-- The four lemmas below are definitional, and private because they only serve the constructions
-- in this file: the first two are the `FGModuleCat`-level readings of
-- `CategoryTheory.ConcreteCategory.hom_ofHom` and of the componentwise addition of morphisms in a
-- full subcategory, the last two are `CategoryTheory.Action.tensorUnit_ρ` and `Action.tensor_ρ`
-- read on the underlying linear maps rather than on morphisms of `FGModuleCat k`.
private theorem hom_hom_fgOfHom {V W : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W] (f : V →ₗ[k] W) :
    (FGModuleCat.ofHom f).hom.hom = f := (rfl)

private theorem hom_hom_add {V W : FGModuleCat.{u} k} (a b : V ⟶ W) :
    (a + b).hom.hom = a.hom.hom + b.hom.hom := (rfl)

private theorem fdRep_tensorUnit_ρ (g : G) :
    (𝟙_ (FDRep k G)).ρ g = LinearMap.id := (rfl)

private theorem fdRep_tensor_ρ (X Y : FDRep k G) (g : G) :
    (X ⊗ Y).ρ g = TensorProduct.map (X.ρ g) (Y.ρ g) := (rfl)

/-- **An isomorphism in `FDRep k G` from an equivariant linear equivalence.** This is
`CategoryTheory.Action.mkIso` for `FDRep k G`, with the commutation condition stated pointwise on
the underlying linear maps instead of as an equation of morphisms of `FGModuleCat k`. -/
noncomputable def fdRepIsoOfEquivariant {X Y : FDRep k G} (e : X ≃ₗ[k] Y)
    (he : ∀ (g : G) (x : X), e (X.ρ g x) = Y.ρ g (e x)) : X ≅ Y :=
  Action.mkIso (LinearEquiv.toFGModuleCatIso e) fun g => by
    apply FGModuleCat.hom_ext
    rw [FGModuleCat.hom_hom_comp, FGModuleCat.hom_hom_comp, FDRep.hom_hom_action_ρ,
      FDRep.hom_hom_action_ρ]
    exact LinearMap.ext (he g)

/-- **Base change of an equivariant map.** An equivariant map `V → W` extends to the equivariant
map `k' ⊗[k] V → k' ⊗[k] W` that acts on the second factor. -/
noncomputable def baseChangeFDRepHom {V W : FDRep k G} (φ : V ⟶ W) :
    (FDRep.of (Representation.baseChange k' V.ρ) : FDRep k' G) ⟶
      FDRep.of (Representation.baseChange k' W.ρ) where
  hom := FGModuleCat.ofHom (LinearMap.baseChange k' φ.hom.hom.hom)
  comm g := by
    apply FGModuleCat.hom_ext
    rw [FGModuleCat.hom_hom_comp, FGModuleCat.hom_hom_comp, FDRep.hom_hom_action_ρ,
      FDRep.hom_hom_action_ρ, FDRep.of_ρ', FDRep.of_ρ', Representation.baseChange_apply,
      Representation.baseChange_apply, hom_hom_fgOfHom, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp]
    refine congrArg (LinearMap.baseChange k') ?_
    simpa [FGModuleCat.hom_hom_comp] using
      congrArg (fun t : V.V ⟶ W.V => t.hom.hom) (φ.comm g)

/-- The linear map underlying the base change of an equivariant map is the base change of the
linear map underlying it. -/
@[simp]
theorem baseChangeFDRepHom_hom_hom_hom {V W : FDRep k G} (φ : V ⟶ W) :
    (baseChangeFDRepHom k' φ).hom.hom.hom = LinearMap.baseChange k' φ.hom.hom.hom := (rfl)

/-- **Base change of equivariant maps is additive.** -/
theorem baseChangeFDRepHom_add {V W : FDRep k G} (φ ψ : V ⟶ W) :
    baseChangeFDRepHom k' (φ + ψ) = baseChangeFDRepHom k' φ + baseChangeFDRepHom k' ψ := by
  apply Action.hom_ext
  apply FGModuleCat.hom_ext
  rw [baseChangeFDRepHom_hom_hom_hom, Action.add_hom, hom_hom_add, Action.add_hom, hom_hom_add,
    baseChangeFDRepHom_hom_hom_hom, baseChangeFDRepHom_hom_hom_hom, LinearMap.baseChange_add]

/-- **Scalar extension as a functor on finite-dimensional representations.** It sends a
representation `V` of `G` over `k` to `k' ⊗[k] V` with `g` acting by `1 ⊗ V.ρ g`, and an
equivariant map to its base change. -/
noncomputable def baseChangeFDRep : FDRep k G ⥤ FDRep k' G where
  obj V := FDRep.of (Representation.baseChange k' V.ρ)
  map φ := baseChangeFDRepHom k' φ
  map_id V := by
    apply Action.hom_ext
    apply FGModuleCat.hom_ext
    rw [baseChangeFDRepHom_hom_hom_hom, Action.id_hom, FGModuleCat.hom_hom_id,
      LinearMap.baseChange_id, Action.id_hom, FGModuleCat.hom_hom_id]
  map_comp φ ψ := by
    apply Action.hom_ext
    apply FGModuleCat.hom_ext
    rw [baseChangeFDRepHom_hom_hom_hom, Action.comp_hom, FGModuleCat.hom_hom_comp,
      LinearMap.baseChange_comp, Action.comp_hom, FGModuleCat.hom_hom_comp,
      baseChangeFDRepHom_hom_hom_hom, baseChangeFDRepHom_hom_hom_hom]

/-- The functor takes a representation to its scalar extension.

Deliberately not a `simp` lemma: it is an equation between *objects* of `FDRep k' G`, which has
no business in the global `simp` set. -/
theorem baseChangeFDRep_obj (V : FDRep k G) :
    (baseChangeFDRep k').obj V = FDRep.of (Representation.baseChange k' V.ρ) := (rfl)

/-- The functor takes an equivariant map to its base change. -/
theorem baseChangeFDRep_map {V W : FDRep k G} (φ : V ⟶ W) :
    (baseChangeFDRep k').map φ = baseChangeFDRepHom k' φ := (rfl)

instance : (baseChangeFDRep (k := k) k' (G := G)).Additive where
  map_add {_ _ φ ψ} := baseChangeFDRepHom_add k' φ ψ

/-- **The tensor unit is preserved**: `k' ⊗[k] k` is the trivial one-dimensional representation
over `k'`. -/
noncomputable def baseChangeFDRepUnitIso :
    (FDRep.of (Representation.baseChange k' (𝟙_ (FDRep k G)).ρ) : FDRep k' G) ≅
      𝟙_ (FDRep k' G) :=
  fdRepIsoOfEquivariant (AlgebraTensorModule.rid k k' k') fun g z => by
    rw [FDRep.of_ρ', Representation.baseChange_apply, fdRep_tensorUnit_ρ, fdRep_tensorUnit_ρ]
    induction z using TensorProduct.inductionOn with
    | tmul a x => simp
    | add x y hx hy => simp_all

/-- **Tensor products are preserved**: extending the scalars of a tensor product of
representations gives the tensor product over `k'` of the extensions. -/
noncomputable def baseChangeFDRepTensorIso (X Y : FDRep k G) :
    (FDRep.of (Representation.baseChange k' (X ⊗ Y).ρ) : FDRep k' G) ≅
      FDRep.of (Representation.baseChange k' X.ρ) ⊗
        FDRep.of (Representation.baseChange k' Y.ρ) :=
  fdRepIsoOfEquivariant (AlgebraTensorModule.distribBaseChange k k' X Y) fun g z => by
    rw [FDRep.of_ρ', Representation.baseChange_apply, fdRep_tensor_ρ, fdRep_tensor_ρ,
      FDRep.of_ρ', FDRep.of_ρ', Representation.baseChange_apply,
      Representation.baseChange_apply]
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
        induction x using TensorProduct.inductionOn with
        | tmul p q =>
            rw [LinearMap.baseChange_tmul, TensorProduct.map_tmul,
              AlgebraTensorModule.distribBaseChange_tmul,
              AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul,
              LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
        | add p q hp hq => simp only [map_add, tmul_add, hp, hq]
    | add x y hx hy => simp_all

section Exact

/-- The forgetful functor from finite-dimensional representations to `K`-modules. -/
private noncomputable abbrev fdRepForget (K : Type u) [Field K] :
    FDRep K G ⥤ ModuleCat.{u} K :=
  Action.forget (FGModuleCat K) G ⋙ forget₂ (FGModuleCat K) (ModuleCat K)

/-- **Base change is exact.** A short exact sequence of finite-dimensional representations over
`k` stays short exact after extending the scalars to `k'`: the forgetful functor to `k'`-modules
is faithful and exact, so it is enough to see the extension as `k' ⊗[k] -` on the underlying
`k`-modules, where flatness of `k'` over `k` preserves injectivity, exactness and
surjectivity. -/
theorem shortExact_map_baseChangeFDRep {S : ShortComplex (FDRep k G)} (hS : S.ShortExact) :
    (S.map (baseChangeFDRep k')).ShortExact := by
  refine ShortExact.reflects_shortExact_of_faithful (fdRepForget k') ?_
  have hk := hS.map_of_exact (fdRepForget k)
  rw [← ShortComplex.map_comp]
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · exact Module.Flat.lTensor_exact k'
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hk.exact)
  · exact Module.Flat.lTensor_preserves_injective_linearMap _ hk.moduleCat_injective_f
  · exact LinearMap.lTensor_surjective k' hk.moduleCat_surjective_g

/-- Base change is exact for the canonical exact structures on `FDRep k G` and `FDRep k' G`. -/
theorem isConflationExact_baseChangeFDRep :
    (ExactStructure.abelian (FDRep k G)).IsConflationExact
      (ExactStructure.abelian (FDRep k' G)) (baseChangeFDRep k') where
  map_conflation hS := (ExactStructure.abelian_conflation _).2
    (shortExact_map_baseChangeFDRep k' ((ExactStructure.abelian_conflation _).1 hS))

end Exact

section K0

/-- **Base change on the Grothendieck ring.** Extending the scalars from `k` to `k'` is a ring
homomorphism `G₀(k[G]) → G₀(k'[G])` between the exact Grothendieck rings of finite-dimensional
representations, taking `[V]` to `[k' ⊗[k] V]`. It is additive because base change is exact
(`TauCeti.isConflationExact_baseChangeFDRep`), and multiplicative because base change preserves
the tensor unit and tensor products. -/
noncomputable def baseChangeK0 :
    ExactK0.{max u v} (ExactStructure.abelian (FDRep k G)) →+*
      ExactK0.{max u v} (ExactStructure.abelian (FDRep k' G)) :=
  ExactK0.liftRingHom
    { obj := fun V => ExactK0.of (FDRep.of (Representation.baseChange k' V.ρ))
      map_conflation := fun {_} hS =>
        ExactK0.of_conflation ((isConflationExact_baseChangeFDRep k').map_conflation hS) }
    (by rw [ExactK0.one_def]; exact ExactK0.of_congr (baseChangeFDRepUnitIso k'))
    fun X Y => by
      rw [ExactK0.of_mul_of]
      exact ExactK0.of_congr (baseChangeFDRepTensorIso k' X Y)

/-- Base change sends the class of a representation to the class of its scalar extension. -/
@[simp]
theorem baseChangeK0_of (V : FDRep k G) :
    baseChangeK0 k' (ExactK0.of V) =
      ExactK0.of (FDRep.of (Representation.baseChange k' V.ρ)) :=
  ExactK0.liftRingHom_of _ _ _ V

/-- **Base change along the identity is the identity**: `k ⊗[k] V` is `V`. -/
@[simp]
theorem baseChangeK0_id : baseChangeK0 (k := k) k (G := G) = RingHom.id _ :=
  ExactK0.ringHom_ext fun V => by
    rw [baseChangeK0_of, RingHom.id_apply]
    exact ExactK0.of_congr (fdRepIsoOfEquivariant (TensorProduct.lid k V) fun g z => by
      rw [FDRep.of_ρ', Representation.baseChange_apply]
      induction z using TensorProduct.inductionOn with
      | tmul a x => simp
      | add x y hx hy => simp_all)

/-- **Base change of a permutation class.** The class of `k[X]` goes to the class of
`k'[X]`: both sides are free on the basis `X`, and the two actions permute that basis in the same
way. -/
theorem baseChangeK0_of_ofMulAction (X : Type u) [MulAction G X] [Finite X] :
    baseChangeK0 k' (ExactK0.of (FDRep.of (Representation.ofMulAction k G X))) =
      ExactK0.of (FDRep.of (Representation.ofMulAction k' G X)) := by
  rw [baseChangeK0_of, FDRep.of_ρ']
  refine ExactK0.of_congr (fdRepIsoOfEquivariant
    (baseChangeOfMulActionEquiv k k' G X).toLinearEquiv fun g x => ?_)
  rw [FDRep.of_ρ', FDRep.of_ρ']
  exact Representation.IntertwiningMap.isIntertwining _ _
    (baseChangeOfMulActionEquiv k k' G X).toIntertwiningMap g x

variable (k'' : Type u) [Field k''] [Algebra k' k''] [Algebra k k'']
  [IsScalarTower k k' k'']

/-- **Base change is transitive along a tower of fields**: extending the scalars from `k` to `k'`
and then to `k''` is extending them from `k` to `k''`, because
`k'' ⊗[k'] (k' ⊗[k] V) ≅ k'' ⊗[k] V`. -/
theorem baseChangeK0_comp :
    (baseChangeK0 (k := k') k'' (G := G)).comp (baseChangeK0 (k := k) k' (G := G)) =
      baseChangeK0 (k := k) k'' :=
  ExactK0.ringHom_ext fun V => by
    rw [RingHom.comp_apply, baseChangeK0_of, baseChangeK0_of, baseChangeK0_of, FDRep.of_ρ']
    exact ExactK0.of_congr (fdRepIsoOfEquivariant
      (AlgebraTensorModule.cancelBaseChange k k' k'' k'' V) fun g z => by
        rw [FDRep.of_ρ', Representation.baseChange_apply]
        induction z using TensorProduct.inductionOn with
        | tmul a x =>
            induction x using TensorProduct.inductionOn with
            | tmul b y => simp
            | add p q hp hq => simp only [map_add, tmul_add, hp, hq]
        | add x y hx hy => simp_all)

end K0

end TauCeti
