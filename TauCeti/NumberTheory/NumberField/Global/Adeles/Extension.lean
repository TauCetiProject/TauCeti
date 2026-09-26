/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Extension

/-!
# The adele ring along a field extension

For an extension `L / K`, every infinite place `w` of `L` lies over its restriction
`w.comap (algebraMap K L)` to `K`, and Mathlib's `NumberField.LiesOver.completionMap` is the
continuous extension `K_{w.comap (algebraMap K L)} → L_w` of `K → L`. Placewise, these maps
assemble into a ring homomorphism `K_∞ → L_∞` of infinite adele rings. Together with the finite
part `IsDedekindDomain.finiteAdeleExtension`, they give the extension map `𝔸_K → 𝔸_L` of adele
rings, which sends an adele `(a_v)_v` to `(a_{v(w)})_w`, where `v(w)` is the place of `K` below
`w`.

These are the maps along which the adeles and ideles of `K` and `L` are compared, for instance
under base change and norm.

## Main results

* `NumberField.infiniteAdeleExtension`, `NumberField.adeleExtension`: the extension maps of
  infinite adele rings and of adele rings.
* `NumberField.continuous_infiniteAdeleExtension`, `NumberField.continuous_adeleExtension`: they
  are continuous.
* `NumberField.infiniteAdeleExtension_algebraMap`, `NumberField.adeleExtension_algebraMap`: they
  extend `K → L` along the diagonal embeddings.
* `NumberField.eq_infiniteAdeleExtension_of_continuous`: for a number field `K`, the infinite
  extension map is the only continuous ring homomorphism with that property, because `K` is dense
  in `K_∞`.
* `NumberField.infiniteAdeleExtension_comp`, `NumberField.adeleExtension_comp`,
  `NumberField.infiniteAdeleExtension_self`, `NumberField.adeleExtension_self`: the tower
  composition and identity laws.
* `NumberField.infiniteAdeleExtensionAlgebra`, `NumberField.adeleExtensionAlgebra`: the induced
  algebra structures, available in the corresponding scopes.

## Provenance

These maps follow the FLT project's adele base-change construction
(`github.com/ImperialCollegeLondon/FLT`, `FLT/NumberField/InfiniteAdeleRing.lean` and
`FLT/NumberField/AdeleRing.lean`; Kevin Buzzard et al., Apache-2.0).
The finite component is described more specifically in `FiniteAdeleRing/Extension.lean`.
-/

public section

open IsDedekindDomain

namespace NumberField

section Infinite

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The extension map of infinite adele rings along `L / K`: the component at an infinite place `w`
of `L` is the image of the component at `w.comap (algebraMap K L)` under the completion map
`K_{w.comap (algebraMap K L)} → L_w`. -/
noncomputable def infiniteAdeleExtension : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  RingHom.pi fun w ↦
    LiesOver.completionMap.comp (Pi.evalRingHom _ (w.comap (algebraMap K L)))

variable {K L} in
/-- The component of `infiniteAdeleExtension K L x` at `w` is the image of the component of `x` at
`w.comap (algebraMap K L)`. -/
@[simp]
theorem infiniteAdeleExtension_apply (x : InfiniteAdeleRing K) (w : InfinitePlace L) :
    infiniteAdeleExtension K L x w = LiesOver.completionMap (x (w.comap (algebraMap K L))) :=
  (rfl)

/-- The extension map of infinite adele rings is continuous. -/
@[continuity, fun_prop]
theorem continuous_infiniteAdeleExtension : Continuous (infiniteAdeleExtension K L) :=
  continuous_pi fun _ ↦ LiesOver.continuous_completionMap.comp (continuous_apply _)

/-- The extension map of infinite adele rings extends `K → L` along the diagonal embeddings. -/
@[simp]
theorem infiniteAdeleExtension_algebraMap (x : K) :
    infiniteAdeleExtension K L (algebraMap K (InfiniteAdeleRing K) x) =
      algebraMap L (InfiniteAdeleRing L) (algebraMap K L x) := by
  funext w
  rw [infiniteAdeleExtension_apply, InfiniteAdeleRing.algebraMap_apply,
    InfiniteAdeleRing.algebraMap_apply, LiesOver.completionMap_coe]
  -- These `WithAbs` lemmas identify the underlying type synonyms on the two sides.
  simp only [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]

/-- For a number field `K`, `infiniteAdeleExtension` is the only continuous ring homomorphism of
infinite adele rings extending `K → L` along the diagonal embeddings: `K` is dense in `K_∞`, and
`L_∞` is Hausdorff. -/
theorem eq_infiniteAdeleExtension_of_continuous [NumberField K]
    {f : InfiniteAdeleRing K →+* InfiniteAdeleRing L} (hf : Continuous f)
    (hfK : ∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) :
    f = infiniteAdeleExtension K L :=
  DFunLike.coe_injective <| (InfiniteAdeleRing.denseRange_algebraMap K).equalizer hf
    (continuous_infiniteAdeleExtension K L) (funext fun x ↦ by simp [hfK])

/-- The extension maps of infinite adele rings compose in a tower `K ⊆ L ⊆ M`. -/
@[simp]
theorem infiniteAdeleExtension_comp (M : Type*) [Field M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (infiniteAdeleExtension L M).comp (infiniteAdeleExtension K L) =
      infiniteAdeleExtension K M := by
  ext x
  funext w
  simp only [RingHom.comp_apply, infiniteAdeleExtension_apply]
  let v := (w.comap (algebraMap L M)).comap (algebraMap K L)
  have hv : v = w.comap (algebraMap K M) := by
    dsimp [v]
    rw [← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq K L M]
  let hwo : w.LiesOver v := hv.symm ▸ inferInstance
  have h :
      (LiesOver.completionMap (v := w.comap (algebraMap L M)) (w := w)).comp
        (LiesOver.completionMap (v := v) (w := w.comap (algebraMap L M))) =
        @LiesOver.completionMap K M _ _ _ v w hwo := by
    apply DFunLike.coe_injective
    apply (InfinitePlace.Completion.denseRange_coe v).equalizer
      (LiesOver.continuous_completionMap.comp LiesOver.continuous_completionMap)
      LiesOver.continuous_completionMap
    funext y
    simp [Function.comp_apply, LiesOver.completionMap_coe,
      WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply,
      ← IsScalarTower.algebraMap_apply]
  calc
    _ = (@LiesOver.completionMap K M _ _ _ v w hwo) (x v) :=
      RingHom.congr_fun h (x v)
    _ = _ := by
      have htransport (p q : InfinitePlace K) (hp : w.LiesOver p) (hq : w.LiesOver q)
          (heq : p = q) :
          (@LiesOver.completionMap K M _ _ _ p w hp) (x p) =
            (@LiesOver.completionMap K M _ _ _ q w hq) (x q) := by
        cases heq
        rfl
      exact htransport v (w.comap (algebraMap K M)) hwo inferInstance hv

/-- Extension of infinite adeles along the identity extension is the identity map. -/
@[simp]
theorem infiniteAdeleExtension_self :
    infiniteAdeleExtension K K = RingHom.id (InfiniteAdeleRing K) := by
  ext x
  funext w
  simp only [infiniteAdeleExtension_apply, RingHom.id_apply, Algebra.algebraMap_self,
    InfinitePlace.comap_id]
  have hwo : w.LiesOver w := ⟨rfl⟩
  have h : (LiesOver.completionMap (v := w) (w := w)) = RingHom.id _ := by
    apply DFunLike.coe_injective
    apply (InfinitePlace.Completion.denseRange_coe w).equalizer
      LiesOver.continuous_completionMap continuous_id
    funext y
    simp [Function.comp_apply, LiesOver.completionMap_coe,
      WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]
  exact RingHom.congr_fun h (x w)

/-- The algebra structure on infinite adeles induced by `infiniteAdeleExtension`, available in
the `InfiniteAdeleExtension` scope. -/
@[reducible]
noncomputable def infiniteAdeleExtensionAlgebra :
    Algebra (InfiniteAdeleRing K) (InfiniteAdeleRing L) :=
  (infiniteAdeleExtension K L).toAlgebra

scoped[InfiniteAdeleExtension] attribute [instance]
  NumberField.infiniteAdeleExtensionAlgebra

open scoped InfiniteAdeleExtension

/-- The algebra map of `infiniteAdeleExtensionAlgebra` is the infinite extension map. -/
@[simp]
theorem algebraMap_infiniteAdeleExtensionAlgebra :
    algebraMap (InfiniteAdeleRing K) (InfiniteAdeleRing L) =
      infiniteAdeleExtension K L :=
  RingHom.algebraMap_toAlgebra _

end Infinite

section Adele

variable (R K B L : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing B] [IsDedekindDomain B] [Algebra R B] [Algebra.IsIntegral R B]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Algebra B L] [IsFractionRing B L]
  [IsScalarTower R B L]

/-- The extension map of adele rings along an integral extension `B / R` of Dedekind domains with
fraction fields `L / K`: `infiniteAdeleExtension` on the infinite component and
`finiteAdeleExtension` on the finite component. -/
noncomputable def adeleExtension : AdeleRing R K →+* AdeleRing B L :=
  (infiniteAdeleExtension K L).prodMap (finiteAdeleExtension R K B L)

variable {R K B L} in
/-- The infinite component of `adeleExtension R K B L a` is the infinite extension of the infinite
component of `a`. -/
@[simp]
theorem adeleExtension_fst (a : AdeleRing R K) :
    (adeleExtension R K B L a).1 = infiniteAdeleExtension K L a.1 :=
  (rfl)

variable {R K B L} in
/-- The finite component of `adeleExtension R K B L a` is the finite extension of the finite
component of `a`. -/
@[simp]
theorem adeleExtension_snd (a : AdeleRing R K) :
    (adeleExtension R K B L a).2 = finiteAdeleExtension R K B L a.2 :=
  (rfl)

/-- The extension map of adele rings is continuous. -/
@[continuity, fun_prop]
theorem continuous_adeleExtension : Continuous (adeleExtension R K B L) :=
  (continuous_infiniteAdeleExtension K L).prodMap
    (continuous_finiteAdeleExtension R K B L)

/-- The extension map of adele rings extends `K → L` along the diagonal embeddings. -/
@[simp]
theorem adeleExtension_algebraMap (x : K) :
    adeleExtension R K B L (algebraMap K (AdeleRing R K) x) =
      algebraMap L (AdeleRing B L) (algebraMap K L x) := by
  refine Prod.ext ?_ ?_
  · rw [adeleExtension_fst, AdeleRing.algebraMap_fst, AdeleRing.algebraMap_fst]
    exact infiniteAdeleExtension_algebraMap K L x
  · rw [adeleExtension_snd, AdeleRing.algebraMap_snd, AdeleRing.algebraMap_snd]
    exact finiteAdeleExtension_algebraMap R K B L x

/-- The extension maps of adele rings compose in a tower `K ⊆ L ⊆ M`. -/
@[simp]
theorem adeleExtension_comp (C M : Type*) [CommRing C] [IsDedekindDomain C]
    [Algebra B C] [Algebra.IsIntegral B C] [Field M] [Algebra L M] [Algebra B M]
    [IsScalarTower B L M] [Algebra C M] [IsFractionRing C M] [IsScalarTower B C M] [Algebra R C]
    [Algebra.IsIntegral R C] [Algebra K M] [Algebra R M] [IsScalarTower R K M]
    [IsScalarTower R C M] [IsScalarTower K L M] :
    (adeleExtension B L C M).comp (adeleExtension R K B L) = adeleExtension R K C M := by
  ext a : 1
  refine Prod.ext ?_ ?_
  · simp only [RingHom.comp_apply, adeleExtension_fst]
    exact RingHom.congr_fun (infiniteAdeleExtension_comp K L M) a.1
  · simp only [RingHom.comp_apply, adeleExtension_snd]
    exact RingHom.congr_fun (finiteAdeleExtension_comp R K B L C M) a.2

/-- Extension of adeles along the identity extension is the identity map. -/
@[simp]
theorem adeleExtension_self : adeleExtension R K R K = RingHom.id (AdeleRing R K) := by
  ext a : 1
  refine Prod.ext ?_ ?_
  · simpa only [adeleExtension_fst, RingHom.id_apply] using
      RingHom.congr_fun (infiniteAdeleExtension_self K) a.1
  · simpa only [adeleExtension_snd, RingHom.id_apply] using
      RingHom.congr_fun (finiteAdeleExtension_self R K) a.2

/-- The algebra structure on adeles induced by `adeleExtension`, available in the
`AdeleExtension` scope. -/
@[reducible]
noncomputable def adeleExtensionAlgebra : Algebra (AdeleRing R K) (AdeleRing B L) :=
  (adeleExtension R K B L).toAlgebra

scoped[AdeleExtension] attribute [instance] NumberField.adeleExtensionAlgebra

open scoped AdeleExtension

/-- The algebra map of `adeleExtensionAlgebra` is the adele extension map. -/
@[simp]
theorem algebraMap_adeleExtensionAlgebra :
    algebraMap (AdeleRing R K) (AdeleRing B L) = adeleExtension R K B L :=
  RingHom.algebraMap_toAlgebra _

end Adele

end NumberField
