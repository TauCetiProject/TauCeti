/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import TauCeti.Algebra.Category.FrobeniusModuleCat.Basic
public import TauCeti.Algebra.Homology.CochainComplex.Double

/-!
# Frobenius cohomology of linearized Frobenius modules

Let `M` be a linearized Frobenius module over `(S, σ)`, with `σ`-semilinear Frobenius `F`. The
*Frobenius cohomology complex* of `M` is the two-term complex

`M --(F - 1)--> M`

in degrees `0` and `1`. The differential `F - 1` is not `S`-linear: on `S = 𝔽_p[U]` with
`F = σ` the `p`-power map, `(F - 1) U = U ^ p - U` while `U • (F - 1) 1 = 0`. It is linear over
the fixed ring `S^{σ = 1}`, the subring `σ.eqLocus (RingHom.id S)` of elements with `σ a = a`,
because `F (a • m) = σ a • F m = a • F m` for such `a`. So the complex is a cochain complex of
`S^{σ = 1}`-modules, indexed by `ℤ`.

Its cohomology is concentrated in degrees `0` and `1`: `H⁰` is the module of Frobenius-fixed
vectors `ker (F - 1) = {m | F m = m}` and `H¹` is the cokernel `M ⧸ (F - 1) M`, through the actual
inclusion into and projection from `M`. For the `p`-power Frobenius of an `𝔽_p`-algebra `S`, the
fixed ring consists of the locally constant `𝔽_p`-valued functions on `Spec S`
(`TauCeti.frobeniusFixedIdempotentEquiv`), which is bigger than `𝔽_p` when `Spec S` is
disconnected. A morphism of linearized Frobenius modules commutes with `F - 1`, so the
construction is a functor, and the identifications of `H⁰` and `H¹` are natural.

## Main definitions

* `TauCeti.FrobeniusModuleCat.frobeniusSubOne`: the `S^{σ = 1}`-linear map `F - 1`.
* `TauCeti.FrobeniusModuleCat.cochainComplex`: the Frobenius cohomology complex
  `M --(F - 1)--> M` in degrees `0` and `1`, with its terms `cochainComplexXIso₀` and
  `cochainComplexXIso₁` and its differential `cochainComplex_d`.
* `TauCeti.FrobeniusModuleCat.cochainComplexFunctor`: the Frobenius cohomology complex as a
  functor to cochain complexes of `S^{σ = 1}`-modules.
* `TauCeti.FrobeniusModuleCat.homologyZeroIso` and `TauCeti.FrobeniusModuleCat.homologyOneIso`:
  the identifications `H⁰ ≅ ker (F - 1)` and `H¹ ≅ M ⧸ range (F - 1)`.

## Main results

* `TauCeti.FrobeniusModuleCat.mem_ker_frobeniusSubOne`: the kernel of `F - 1` consists of the
  vectors fixed by the Frobenius.
* `TauCeti.FrobeniusModuleCat.homologyπ_homologyZeroIso_hom_subtype`: under `homologyZeroIso`, the
  inclusion of the fixed vectors into `M` is the inclusion of the degree-`0` cycles.
* `TauCeti.FrobeniusModuleCat.mkQ_homologyOneIso_inv_homologyι`: under `homologyOneIso`, the
  projection of `M` onto `M ⧸ range (F - 1)` is the projection onto the degree-`1` opcycles.
* `TauCeti.FrobeniusModuleCat.homologyZeroIso_hom_naturality` and
  `TauCeti.FrobeniusModuleCat.homologyOneIso_inv_naturality`: these identifications are natural
  in the linearized Frobenius module.
* `TauCeti.FrobeniusModuleCat.isZero_homology`: the cohomology vanishes outside degrees `0` and
  `1`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Definition 1.5.4.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TauCeti.FrobeniusModuleCat

variable {S : Type u} [CommRing S] {σ : S →+* S}

section frobeniusSubOne

variable (M : FrobeniusModuleCat σ)

/-- The map `F - 1` of a linearized Frobenius module, linear over the fixed ring `S^{σ = 1}`
because the Frobenius is `σ`-semilinear. It is not `S`-linear in general. -/
noncomputable def frobeniusSubOne : M.carrier →ₗ[σ.eqLocus (RingHom.id S)] M.carrier where
  toFun m := M.frobenius m - m
  map_add' m n := by
    rw [map_add]
    abel
  map_smul' a m := by
    have ha : σ a = a := a.prop
    simp only [Subring.smul_def, LinearMap.map_smulₛₗ, ha, RingHom.id_apply, smul_sub]

@[simp]
theorem frobeniusSubOne_apply (m : M.carrier) : M.frobeniusSubOne m = M.frobenius m - m := (rfl)

/-- The kernel of `F - 1` is the module of Frobenius-fixed vectors. -/
theorem mem_ker_frobeniusSubOne {m : M.carrier} :
    m ∈ LinearMap.ker M.frobeniusSubOne ↔ M.frobenius m = m := by
  rw [LinearMap.mem_ker, frobeniusSubOne_apply, sub_eq_zero]

/-- A morphism of linearized Frobenius modules commutes with `F - 1`. -/
theorem map_frobeniusSubOne {N : FrobeniusModuleCat σ} (f : M ⟶ N) (m : M.carrier) :
    f.hom.f (M.frobeniusSubOne m) = N.frobeniusSubOne (f.hom.f m) := by
  rw [frobeniusSubOne_apply, frobeniusSubOne_apply, map_sub, map_frobenius]

end frobeniusSubOne

section Complex

variable (M : FrobeniusModuleCat σ)

/-- The *Frobenius cohomology complex* `M --(F - 1)--> M` of a linearized Frobenius module, a
cochain complex of modules over the fixed ring `S^{σ = 1}` concentrated in degrees `0` and `1`. -/
noncomputable def cochainComplex : CochainComplex (ModuleCat (σ.eqLocus (RingHom.id S))) ℤ :=
  HomologicalComplex.double (ModuleCat.ofHom M.frobeniusSubOne) ComplexShape.up_rel_zero_one

/-- The term of the Frobenius cohomology complex in degree `0` is `M`. -/
noncomputable def cochainComplexXIso₀ :
    M.cochainComplex.X 0 ≅ ModuleCat.of (σ.eqLocus (RingHom.id S)) M.carrier :=
  HomologicalComplex.doubleXIso₀ _ _

/-- The term of the Frobenius cohomology complex in degree `1` is `M`. -/
noncomputable def cochainComplexXIso₁ :
    M.cochainComplex.X 1 ≅ ModuleCat.of (σ.eqLocus (RingHom.id S)) M.carrier :=
  HomologicalComplex.doubleXIso₁ _ _ zero_ne_one

/-- The differential of the Frobenius cohomology complex from degree `0` to degree `1` is
`F - 1`. -/
theorem cochainComplex_d :
    M.cochainComplex.d 0 1 =
      M.cochainComplexXIso₀.hom ≫ ModuleCat.ofHom M.frobeniusSubOne ≫ M.cochainComplexXIso₁.inv :=
  HomologicalComplex.double_d _ _ zero_ne_one

/-- The terms of the Frobenius cohomology complex outside degrees `0` and `1` are zero. -/
theorem isZero_cochainComplex_X (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ 1) :
    IsZero (M.cochainComplex.X n) :=
  HomologicalComplex.isZero_double_X _ _ n h₀ h₁

/-- The `S^{σ = 1}`-linear map underlying a morphism of linearized Frobenius modules, for the
module structures on `M` and `N` restricted to the subring `S^{σ = 1}` of `S`. -/
noncomputable abbrev restrictScalarsHom {M N : FrobeniusModuleCat σ} (f : M ⟶ N) :
    ModuleCat.of (σ.eqLocus (RingHom.id S)) M.carrier ⟶
      ModuleCat.of (σ.eqLocus (RingHom.id S)) N.carrier :=
  ModuleCat.ofHom (f.hom.f.hom.restrictScalars (σ.eqLocus (RingHom.id S)))

variable {M} in
/-- The map of Frobenius cohomology complexes induced by a morphism `f` of linearized Frobenius
modules: `f` in degrees `0` and `1`. -/
noncomputable def cochainComplexMap {N : FrobeniusModuleCat σ} (f : M ⟶ N) :
    M.cochainComplex ⟶ N.cochainComplex :=
  HomologicalComplex.doubleMap _ zero_ne_one (restrictScalarsHom f) (restrictScalarsHom f)
    (by ext m; exact (map_frobeniusSubOne _ f m).symm)

variable {M}

/-- The degree-`0` component of `cochainComplexMap f` is `f`. -/
@[simp]
theorem cochainComplexMap_f_zero {N : FrobeniusModuleCat σ} (f : M ⟶ N) :
    (cochainComplexMap f).f 0 =
      M.cochainComplexXIso₀.hom ≫ restrictScalarsHom f ≫ N.cochainComplexXIso₀.inv :=
  HomologicalComplex.doubleMap_f₀ _ _ _ _ _

/-- The degree-`1` component of `cochainComplexMap f` is `f`. -/
@[simp]
theorem cochainComplexMap_f_one {N : FrobeniusModuleCat σ} (f : M ⟶ N) :
    (cochainComplexMap f).f 1 =
      M.cochainComplexXIso₁.hom ≫ restrictScalarsHom f ≫ N.cochainComplexXIso₁.inv :=
  HomologicalComplex.doubleMap_f₁ _ _ _ _ _

variable (M) in
/-- The identity induces the identity of Frobenius cohomology complexes. -/
@[simp]
theorem cochainComplexMap_id : cochainComplexMap (𝟙 M) = 𝟙 M.cochainComplex :=
  HomologicalComplex.doubleMap_id _ _ _

/-- The map of Frobenius cohomology complexes induced by a composite is the composite. -/
@[simp]
theorem cochainComplexMap_comp {N P : FrobeniusModuleCat σ} (f : M ⟶ N) (g : N ⟶ P) :
    cochainComplexMap (f ≫ g) = cochainComplexMap f ≫ cochainComplexMap g :=
  HomologicalComplex.doubleMap_comp _ _ (restrictScalarsHom f) (restrictScalarsHom f) _
    (restrictScalarsHom g) (restrictScalarsHom g) _

/-- A morphism of linearized Frobenius modules maps Frobenius-fixed vectors to Frobenius-fixed
vectors. -/
theorem ker_frobeniusSubOne_le_comap {N : FrobeniusModuleCat σ} (f : M ⟶ N) :
    LinearMap.ker M.frobeniusSubOne ≤
      (LinearMap.ker N.frobeniusSubOne).comap (restrictScalarsHom f).hom := fun m hm ↦ by
  rw [mem_ker_frobeniusSubOne] at hm
  rw [Submodule.mem_comap, mem_ker_frobeniusSubOne, ModuleCat.hom_ofHom,
    LinearMap.restrictScalars_apply, ← map_frobenius, hm]

/-- A morphism of linearized Frobenius modules maps the image of `F - 1` into the image of
`F - 1`. -/
theorem range_frobeniusSubOne_le_comap {N : FrobeniusModuleCat σ} (f : M ⟶ N) :
    LinearMap.range M.frobeniusSubOne ≤
      (LinearMap.range N.frobeniusSubOne).comap (restrictScalarsHom f).hom := by
  rintro _ ⟨m, rfl⟩
  exact ⟨f.hom.f m, (map_frobeniusSubOne M f m).symm⟩

variable (σ) in
/-- The Frobenius cohomology complex as a functor from linearized Frobenius modules to cochain
complexes of `S^{σ = 1}`-modules. -/
@[expose, simps]
noncomputable def cochainComplexFunctor :
    FrobeniusModuleCat σ ⥤ CochainComplex (ModuleCat (σ.eqLocus (RingHom.id S))) ℤ where
  obj M := M.cochainComplex
  map := cochainComplexMap
  map_id := cochainComplexMap_id
  map_comp := cochainComplexMap_comp

end Complex

section Homology

variable (M : FrobeniusModuleCat σ)

/-- The Frobenius cohomology in degree `0` is the module `ker (F - 1)` of Frobenius-fixed
vectors. -/
noncomputable def homologyZeroIso :
    M.cochainComplex.homology 0 ≅
      ModuleCat.of (σ.eqLocus (RingHom.id S)) (LinearMap.ker M.frobeniusSubOne) :=
  HomologicalComplex.doubleHomologyIso₀ zero_ne_one (ModuleCat.kernelIsLimit _)

/-- Under `homologyZeroIso`, the inclusion of the Frobenius-fixed vectors into `M` is the
inclusion of the cycles in degree `0`. -/
@[reassoc (attr := simp)]
theorem homologyπ_homologyZeroIso_hom_subtype :
    M.cochainComplex.homologyπ 0 ≫ M.homologyZeroIso.hom ≫
        ModuleCat.ofHom (LinearMap.ker M.frobeniusSubOne).subtype =
      M.cochainComplex.iCycles 0 ≫ M.cochainComplexXIso₀.hom :=
  HomologicalComplex.homologyπ_doubleHomologyIso₀_hom_ι zero_ne_one (ModuleCat.kernelIsLimit _)

/-- The Frobenius cohomology in degree `1` is the cokernel `M ⧸ (F - 1) M`. -/
noncomputable def homologyOneIso :
    M.cochainComplex.homology 1 ≅
      ModuleCat.of (σ.eqLocus (RingHom.id S)) (M.carrier ⧸ LinearMap.range M.frobeniusSubOne) :=
  HomologicalComplex.doubleHomologyIso₁ zero_ne_one (ModuleCat.cokernelIsColimit _)

/-- Under `homologyOneIso`, the projection of `M` onto `M ⧸ (F - 1) M` is the projection onto the
opcycles in degree `1`. -/
@[reassoc (attr := simp)]
theorem mkQ_homologyOneIso_inv_homologyι :
    ModuleCat.ofHom (LinearMap.range M.frobeniusSubOne).mkQ ≫ M.homologyOneIso.inv ≫
        M.cochainComplex.homologyι 1 =
      M.cochainComplexXIso₁.inv ≫ M.cochainComplex.pOpcycles 1 :=
  HomologicalComplex.π_doubleHomologyIso₁_inv_homologyι (g := ModuleCat.ofHom M.frobeniusSubOne)
    zero_ne_one (ModuleCat.cokernelIsColimit _)

variable {M} in
/-- The identification of `H⁰` with the Frobenius-fixed vectors is natural: the map induced by a
morphism `f` on `H⁰` is the restriction of `f` to the fixed vectors. -/
theorem homologyZeroIso_hom_naturality {N : FrobeniusModuleCat σ} (f : M ⟶ N) :
    HomologicalComplex.homologyMap (cochainComplexMap f) 0 ≫ N.homologyZeroIso.hom =
      M.homologyZeroIso.hom ≫
        ModuleCat.ofHom ((restrictScalarsHom f).hom.restrict (ker_frobeniusSubOne_le_comap f)) := by
  have : Mono (ModuleCat.ofHom (LinearMap.ker N.frobeniusSubOne).subtype) :=
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  rw [← cancel_mono (ModuleCat.ofHom (LinearMap.ker N.frobeniusSubOne).subtype),
    ← cancel_epi (M.cochainComplex.homologyπ 0)]
  have h : ModuleCat.ofHom ((restrictScalarsHom f).hom.restrict
        (ker_frobeniusSubOne_le_comap f)) ≫
        ModuleCat.ofHom (LinearMap.ker N.frobeniusSubOne).subtype =
      ModuleCat.ofHom (LinearMap.ker M.frobeniusSubOne).subtype ≫ restrictScalarsHom f :=
    (rfl)
  simp [h]

variable {M} in
/-- The identification of `H¹` with `M ⧸ (F - 1) M` is natural: the map induced by a morphism
`f` on `H¹` is the map of quotients induced by `f`. -/
theorem homologyOneIso_inv_naturality {N : FrobeniusModuleCat σ} (f : M ⟶ N) :
    M.homologyOneIso.inv ≫ HomologicalComplex.homologyMap (cochainComplexMap f) 1 =
      ModuleCat.ofHom ((LinearMap.range M.frobeniusSubOne).mapQ _ (restrictScalarsHom f).hom
        (range_frobeniusSubOne_le_comap f)) ≫ N.homologyOneIso.inv := by
  have : Epi (ModuleCat.ofHom (LinearMap.range M.frobeniusSubOne).mkQ) :=
    (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  rw [← cancel_mono (N.cochainComplex.homologyι 1),
    ← cancel_epi (ModuleCat.ofHom (LinearMap.range M.frobeniusSubOne).mkQ)]
  have h : ModuleCat.ofHom (LinearMap.range M.frobeniusSubOne).mkQ ≫
        ModuleCat.ofHom ((LinearMap.range M.frobeniusSubOne).mapQ _ (restrictScalarsHom f).hom
          (range_frobeniusSubOne_le_comap f)) =
      restrictScalarsHom f ≫ ModuleCat.ofHom (LinearMap.range N.frobeniusSubOne).mkQ :=
    (rfl)
  simp [reassoc_of% h]

/-- The Frobenius cohomology vanishes outside degrees `0` and `1`. -/
theorem isZero_homology (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ 1) :
    IsZero (M.cochainComplex.homology n) :=
  HomologicalComplex.isZero_double_homology _ _ n h₀ h₁

end Homology

end TauCeti.FrobeniusModuleCat
