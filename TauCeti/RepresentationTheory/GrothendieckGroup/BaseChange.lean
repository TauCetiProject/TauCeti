/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.GrothendieckGroup.FDRep
-- Non-public: the isomorphism constructor `TauCeti.fdRepIsoOfEquivariant` is used only inside the
-- proofs of `TauCeti.baseChangeK0_id`, `baseChangeK0_of_ofMulAction` and `baseChangeK0_comp`.
import TauCeti.RepresentationTheory.FDRep

/-!
# Base change on the Grothendieck ring of finite-dimensional representations

Let `k` and `k'` be fields with `k'` a `k`-algebra, and let `G` be a monoid. Extending the
scalars of a finite-dimensional representation, `V ↦ k' ⊗[k] V` with `g` acting by `1 ⊗ V.ρ g`, is
the functor `TauCeti.baseChangeFDRep : FDRep k G ⥤ FDRep k' G` of
`TauCeti/RepresentationTheory/BaseChange.lean`. It is additive there, and it is **exact**, because
`k'` is flat over `k`: a short exact sequence of representations stays short exact after
tensoring, which is `Module.Flat.lTensor_exact` together with the preservation of injectivity
and of surjectivity, read through the faithful exact forgetful functor to `k'`-modules.

So base change descends to the exact Grothendieck group, and because it carries the tensor unit
`k` to `k' ⊗[k] k ≅ k'` and a tensor product to a tensor product
(`TauCeti.baseChangeFDRepUnitIso` and `TauCeti.baseChangeFDRepTensorIso`), the descended map is a
homomorphism of rings

```text
baseChangeK0 k' : G₀(k[G]) →+* G₀(k'[G]),   [V] ↦ [k' ⊗[k] V].
```

This is the base-change homomorphism of the Grothendieck rings `R_k(G) → R_{k'}(G)` of Serre,
Part III. It is the comparison along which an identity in `G₀` proved over one field is
transported to an extension of that field -- in particular to a splitting field. It is the
identity for `k' = k`, transitive along a tower, and it takes the class of a permutation
representation `k[X]` to the class of `k'[X]`.

## Main definitions

* `TauCeti.baseChangeK0`: base change on the exact Grothendieck ring, as a ring homomorphism.

## Main results

* `TauCeti.shortExact_map_baseChangeFDRep` and `TauCeti.isConflationExact_baseChangeFDRep`:
  **base change is exact.** They sit here, beside `FDRep.shortExact_map_tensorLeft` in
  `TauCeti/RepresentationTheory/GrothendieckGroup/FDRep.lean`, because preservation of short exact
  sequences in `FDRep` is what the exact Grothendieck group asks of a functor.
* `TauCeti.baseChangeK0_of`: the class of a representation goes to the class of its scalar
  extension.
* `TauCeti.baseChangeK0_id` and `TauCeti.baseChangeK0_comp`: base change along the identity is
  the identity, and base change along a tower is the composite.
* `TauCeti.baseChangeK0_of_ofMulAction`: base change preserves permutation classes.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part III,
  §14.1 and §15.5, for `R_k(G)` and its behaviour under extension of the base field.
-/

public section

open CategoryTheory MonoidalCategory TensorProduct

namespace TauCeti

universe u v

variable {k : Type u} (k' : Type u) [Field k] [Field k'] [Algebra k k'] {G : Type v} [Monoid G]

section Exact

/-- The forgetful functor from finite-dimensional representations to `K`-modules. -/
private noncomputable abbrev fdRepForget (K : Type u) [Field K] :
    FDRep K G ⥤ ModuleCat.{u} K :=
  Action.forget (FGModuleCat K) G ⋙ forget₂ (FGModuleCat K) (ModuleCat K)

/-- The two maps of a short complex of representations, base changed and forgotten to `k'`-modules,
read as `LinearMap.lTensor k'` of the maps forgotten to `k`-modules: this is
`TauCeti.coe_baseChangeFDRepHom_hom_hom_hom` with the functors applied, the form the flatness
lemmas behind `TauCeti.shortExact_map_baseChangeFDRep` are stated in. -/
private theorem coe_map_baseChangeFDRep_f (S : ShortComplex (FDRep k G)) :
    ⇑(ConcreteCategory.hom (S.map (baseChangeFDRep k' ⋙ fdRepForget k')).f) =
      ⇑(LinearMap.lTensor k' (S.map (fdRepForget k)).f.hom) :=
  coe_baseChangeFDRepHom_hom_hom_hom k' S.f

/-- The companion of `TauCeti.coe_map_baseChangeFDRep_f` for the second map of the complex. -/
private theorem coe_map_baseChangeFDRep_g (S : ShortComplex (FDRep k G)) :
    ⇑(ConcreteCategory.hom (S.map (baseChangeFDRep k' ⋙ fdRepForget k')).g) =
      ⇑(LinearMap.lTensor k' (S.map (fdRepForget k)).g.hom) :=
  coe_baseChangeFDRepHom_hom_hom_hom k' S.g

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
  · rw [coe_map_baseChangeFDRep_f, coe_map_baseChangeFDRep_g]
    exact Module.Flat.lTensor_exact k'
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hk.exact)
  · rw [coe_map_baseChangeFDRep_f]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hk.moduleCat_injective_f
  · rw [coe_map_baseChangeFDRep_g]
    exact LinearMap.lTensor_surjective k' hk.moduleCat_surjective_g

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
