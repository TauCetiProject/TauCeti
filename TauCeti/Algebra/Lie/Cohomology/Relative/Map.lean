/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Cohomology.Relative.Basic

/-!
# Maps of relative Lie algebra cochain complexes

A Lie algebra homomorphism carrying one distinguished subalgebra into the other pulls
back relative cochains. An intertwining linear map pushes their coefficient values
forward. For equivariant relative complexes, the pullback also intertwines the indexed
actions on the Lie algebras and on the coefficients. These maps commute with the
Chevalley–Eilenberg differential and induce restriction and coefficient maps on cohomology.

For relative cohomology of Lie groups and naturality of the comparison with continuous
cohomology, see C. Wockel, *Topological group cohomology of Lie groups and Chern–Weil theory
for compact symmetric spaces*, Theorem 3.3. The induced maps on cohomology are given by
`HomologicalComplex.homologyMap`.
-/

public section

open CategoryTheory

namespace TauCeti.LieModule.Cohomology

universe u v w

variable {R : Type u} [CommRing R]
  {L L' L'' : Type v} {M M' M'' : Type w}
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
  [AddCommGroup M''] [Module R M''] [LieRingModule L'' M''] [LieModule R L'' M'']

section Subcomplex

variable {S : ∀ n, Submodule R (L [⋀^Fin n]→ₗ[R] M)}
  {T : ∀ n, Submodule R (L' [⋀^Fin n]→ₗ[R] M')}
  {hS : ∀ n, ∀ ω ∈ S n, d R L M n ω ∈ S (n + 1)}
  {hT : ∀ n, ∀ ω ∈ T n, d R L' M' n ω ∈ T (n + 1)}
  {e : M →ₗ[R] M'} {φ : L' →ₗ⁅R⁆ L}

/-- Restrict a Chevalley–Eilenberg map to subcomplexes that it carries into one another. -/
noncomputable def cochainSubcomplexMap (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (h : ∀ n, ∀ ω ∈ S n, cochainMap e φ n ω ∈ T n) :
    cochainSubcomplex S hS ⟶ cochainSubcomplex T hT :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom ((cochainMap e φ n).restrict (h n))) fun n ↦ by
    rw [cochainSubcomplex_d_succ, cochainSubcomplex_d_succ]
    -- The composition rewrite needs the concrete submodule objects in place of the
    -- degree objects of the two cochain complexes.
    change ModuleCat.ofHom ((cochainSubcomplexD T hT n).comp
        ((cochainMap e φ n).restrict (h n))) =
      ModuleCat.ofHom (((cochainMap e φ (n + 1)).restrict (h (n + 1))).comp
        (cochainSubcomplexD S hS n))
    apply congrArg ModuleCat.ofHom
    exact LinearMap.ext fun ω ↦ Subtype.ext <| by
      simp only [LinearMap.comp_apply, LinearMap.coe_restrict_apply, coe_cochainSubcomplexD]
      exact (cochainMap_d e φ he n ω.val).symm

/-- In each degree, the subcomplex map is the restriction of the ambient cochain map. -/
@[simp]
theorem cochainSubcomplexMap_f (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (h : ∀ n, ∀ ω ∈ S n, cochainMap e φ n ω ∈ T n) (n : ℕ) :
    (cochainSubcomplexMap (hS := hS) (hT := hT) he h).f n =
      ModuleCat.ofHom ((cochainMap e φ n).restrict (h n)) :=
  (rfl)

/-- The inclusions of the subcomplexes intertwine the restricted and ambient maps. -/
@[reassoc (attr := simp)]
theorem cochainSubcomplexMap_comp_subtype
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (h : ∀ n, ∀ ω ∈ S n, cochainMap e φ n ω ∈ T n) :
    cochainSubcomplexMap (hS := hS) (hT := hT) he h ≫ cochainSubcomplexSubtype T hT =
      cochainSubcomplexSubtype S hS ≫ cochainComplexMap e φ he := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, cochainSubcomplexMap_f,
    cochainSubcomplexSubtype_f, cochainSubcomplexSubtype_f, cochainComplexMap_f]
  rfl

/-- Restricting the identity cochain map to a subcomplex gives its identity. -/
@[simp]
theorem cochainSubcomplexMap_id
    {he : ∀ (x : L) (m : M), (LinearMap.id : M →ₗ[R] M)
      ⁅(LieHom.id : L →ₗ⁅R⁆ L) x, m⁆ = ⁅x, LinearMap.id m⁆}
    (h : ∀ n, ∀ ω ∈ S n, cochainMap (LinearMap.id : M →ₗ[R] M)
      (LieHom.id : L →ₗ⁅R⁆ L) n ω ∈ S n) :
    cochainSubcomplexMap (hS := hS) (hT := hS) he h = 𝟙 (cochainSubcomplex S hS) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [cochainSubcomplexMap_f, HomologicalComplex.id_f]
  -- The identity lemma for bundled linear maps needs the concrete submodule as its object.
  change ModuleCat.ofHom _ = ModuleCat.ofHom (LinearMap.id : S n →ₗ[R] S n)
  apply congrArg ModuleCat.ofHom
  exact LinearMap.ext fun ω ↦ Subtype.ext <| by
    simp only [LinearMap.coe_restrict_apply, LinearMap.id_apply, cochainMap_id]

variable {U : ∀ n, Submodule R (L'' [⋀^Fin n]→ₗ[R] M'')}
  {hU : ∀ n, ∀ ω ∈ U n, d R L'' M'' n ω ∈ U (n + 1)}
  {e' : M' →ₗ[R] M''} {ψ : L'' →ₗ⁅R⁆ L'}

/-- Restricting cochain maps to subcomplexes commutes with composition. -/
theorem cochainSubcomplexMap_comp (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (he' : ∀ (x : L'') (m : M'), e' ⁅ψ x, m⁆ = ⁅x, e' m⁆)
    (h : ∀ n, ∀ ω ∈ S n, cochainMap e φ n ω ∈ T n)
    (h' : ∀ n, ∀ ω ∈ T n, cochainMap e' ψ n ω ∈ U n)
    (hcomp : ∀ n, ∀ ω ∈ S n, cochainMap (e'.comp e) (φ.comp ψ) n ω ∈ U n) :
    cochainSubcomplexMap (hS := hS) (hT := hT) he h ≫
      cochainSubcomplexMap (hS := hT) (hT := hU) he' h' =
      cochainSubcomplexMap (hS := hS) (hT := hU) (fun x m ↦ by simp [he, he']) hcomp := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, cochainSubcomplexMap_f, cochainSubcomplexMap_f,
    cochainSubcomplexMap_f]
  -- Identify the degree objects with their submodules before comparing the linear maps.
  change ModuleCat.ofHom (((cochainMap e' ψ n).restrict (h' n)).comp
    ((cochainMap e φ n).restrict (h n))) = _
  apply congrArg ModuleCat.ofHom
  exact LinearMap.ext fun ω ↦ Subtype.ext <| by
    simpa only [LinearMap.comp_apply, LinearMap.coe_restrict_apply] using
      DFunLike.congr_fun (cochainMap_comp e e' φ ψ n) ω.val

end Subcomplex

section Relative

variable {H : LieSubalgebra R L} {H' : LieSubalgebra R L'} {H'' : LieSubalgebra R L''}
  {e : M →ₗ[R] M'} {φ : L' →ₗ⁅R⁆ L}

/-- Pullback and coefficient change preserve relative cochains when the Lie algebra map
carries the distinguished subalgebra into the distinguished subalgebra. -/
private theorem cochainMap_mem_relativeCochains
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (hφ : ∀ x ∈ H', φ x ∈ H) {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ relativeCochains R M H n) :
    cochainMap e φ n ω ∈ relativeCochains R M' H' n := by
  obtain ⟨hhoriz, hinv⟩ := mem_relativeCochains_iff.mp hω
  refine mem_relativeCochains_iff.mpr ⟨fun v i hi ↦ ?_, fun x hx ↦ ?_⟩
  · rw [cochainMap_apply, hhoriz _ i (hφ _ hi), map_zero]
  · rw [← cochainMap_lie e φ he, hinv _ (hφ _ hx), map_zero]

/-- Pullback along a Lie algebra map preserving the distinguished subalgebras, followed by an
intertwining map of coefficients, as a morphism of relative Chevalley–Eilenberg complexes. -/
noncomputable def relativeCochainComplexMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (hφ : ∀ x ∈ H', φ x ∈ H) :
    relativeCochainComplex R M H ⟶ relativeCochainComplex R M' H' :=
  cochainSubcomplexMap he fun _ _ ↦ cochainMap_mem_relativeCochains he hφ

/-- The relative cochain map pulls back each argument and applies the coefficient map. -/
@[simp]
theorem relativeCochainComplexMap_f_apply
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (hφ : ∀ x ∈ H', φ x ∈ H) (n : ℕ) (ω : relativeCochains R M H n) (v : Fin n → L') :
    Subtype.val (α := L' [⋀^Fin n]→ₗ[R] M') ((relativeCochainComplexMap e φ he hφ).f n ω) v =
      e (ω.val fun i ↦ φ (v i)) := by
  rw [relativeCochainComplexMap, cochainSubcomplexMap_f]
  exact cochainMap_apply e φ ω.val v

/-- Identity Lie algebra and coefficient maps act identically on relative cochains. -/
@[simp]
theorem relativeCochainComplexMap_id :
    relativeCochainComplexMap (H := H) (H' := H) LinearMap.id LieHom.id
        (fun _ _ ↦ rfl) (fun _ hx ↦ hx) = 𝟙 (relativeCochainComplex R M H) := by
  exact cochainSubcomplexMap_id _

/-- Relative cochain maps compose contravariantly in the Lie algebra and covariantly
in the coefficients. -/
theorem relativeCochainComplexMap_comp (e' : M' →ₗ[R] M'') (ψ : L'' →ₗ⁅R⁆ L')
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (he' : ∀ (x : L'') (m : M'), e' ⁅ψ x, m⁆ = ⁅x, e' m⁆)
    (hφ : ∀ x ∈ H', φ x ∈ H) (hψ : ∀ x ∈ H'', ψ x ∈ H') :
    relativeCochainComplexMap e φ he hφ ≫ relativeCochainComplexMap e' ψ he' hψ =
      relativeCochainComplexMap (e'.comp e) (φ.comp ψ)
        (fun x m ↦ by simp [he, he']) (fun x hx ↦ hφ _ (hψ x hx)) := by
  exact cochainSubcomplexMap_comp he he' _ _ _

end Relative

section Equivariant

variable {H : LieSubalgebra R L} {H' : LieSubalgebra R L'} {H'' : LieSubalgebra R L''}
  {e : M →ₗ[R] M'} {φ : L' →ₗ⁅R⁆ L}
  {K K' K'' : Type*}
  {Ad : K → L →ₗ⁅R⁆ L} {Ad' : K' → L' →ₗ⁅R⁆ L'}
  {Ad'' : K'' → L'' →ₗ⁅R⁆ L''}
  {ρ : K → M →ₗ[R] M} {ρ' : K' → M' →ₗ[R] M'} {ρ'' : K'' → M'' →ₗ[R] M''}
  {hρ : ∀ k x m, ρ k ⁅x, m⁆ = ⁅Ad k x, ρ k m⁆}
  {hρ' : ∀ k x m, ρ' k ⁅x, m⁆ = ⁅Ad' k x, ρ' k m⁆}
  {hρ'' : ∀ k x m, ρ'' k ⁅x, m⁆ = ⁅Ad'' k x, ρ'' k m⁆}
  {f : K' → K}

/-- A relative cochain map preserves equivariance when it intertwines the actions
on the Lie algebras and on the coefficients along the same index map. -/
private theorem cochainMap_mem_equivariantRelativeCochains
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (hφ : ∀ x ∈ H', φ x ∈ H)
    (hAd : ∀ k x, φ (Ad' k x) = Ad (f k) (φ x))
    (hCoeff : ∀ k m, e (ρ (f k) m) = ρ' k (e m))
    {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ equivariantRelativeCochains R M Ad ρ H n) :
    cochainMap e φ n ω ∈ equivariantRelativeCochains R M' Ad' ρ' H' n := by
  obtain ⟨hrel, hEq⟩ := mem_equivariantRelativeCochains_iff.mp hω
  refine mem_equivariantRelativeCochains_iff.mpr
    ⟨cochainMap_mem_relativeCochains he hφ hrel, fun k v ↦ ?_⟩
  simp only [cochainMap_apply, hAd, hEq (f k) (fun i ↦ φ (v i)), hCoeff]

/-- Pullback along a compatible map of pairs and pushforward along a compatible coefficient
map induce a morphism of equivariant relative cochain complexes. -/
noncomputable def equivariantRelativeCochainComplexMap (e : M →ₗ[R] M')
    (φ : L' →ₗ⁅R⁆ L) (f : K' → K) (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (hφ : ∀ x ∈ H', φ x ∈ H)
    (hAd : ∀ k x, φ (Ad' k x) = Ad (f k) (φ x))
    (hCoeff : ∀ k m, e (ρ (f k) m) = ρ' k (e m)) :
    equivariantRelativeCochainComplex R M Ad ρ H hρ ⟶
      equivariantRelativeCochainComplex R M' Ad' ρ' H' hρ' :=
  cochainSubcomplexMap he fun _ _ ↦ cochainMap_mem_equivariantRelativeCochains he hφ hAd hCoeff

/-- The equivariant relative cochain map evaluates by pullback of arguments and coefficient
change. -/
@[simp]
theorem equivariantRelativeCochainComplexMap_f_apply
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (hφ : ∀ x ∈ H', φ x ∈ H)
    (hAd : ∀ k x, φ (Ad' k x) = Ad (f k) (φ x))
    (hCoeff : ∀ k m, e (ρ (f k) m) = ρ' k (e m))
    (n : ℕ) (ω : equivariantRelativeCochains R M Ad ρ H n) (v : Fin n → L') :
    Subtype.val (α := L' [⋀^Fin n]→ₗ[R] M')
        ((equivariantRelativeCochainComplexMap (hρ := hρ) (hρ' := hρ')
          e φ f he hφ hAd hCoeff).f n ω) v =
      e (ω.val fun i ↦ φ (v i)) := by
  rw [equivariantRelativeCochainComplexMap, cochainSubcomplexMap_f]
  exact cochainMap_apply e φ ω.val v

/-- Identity maps act identically on equivariant relative cochains. -/
@[simp]
theorem equivariantRelativeCochainComplexMap_id :
    equivariantRelativeCochainComplexMap (H := H) (H' := H) (hρ := hρ) (hρ' := hρ)
        LinearMap.id LieHom.id id (fun _ _ ↦ rfl) (fun _ hx ↦ hx) (fun _ _ ↦ rfl)
        (fun _ _ ↦ rfl) = 𝟙 (equivariantRelativeCochainComplex R M Ad ρ H hρ) := by
  exact cochainSubcomplexMap_id _

/-- Equivariant relative cochain maps compose in the Lie and index arguments contravariantly
and in the coefficient argument covariantly. -/
theorem equivariantRelativeCochainComplexMap_comp
    (e' : M' →ₗ[R] M'') (ψ : L'' →ₗ⁅R⁆ L') {g : K'' → K'}
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (he' : ∀ (x : L'') (m : M'), e' ⁅ψ x, m⁆ = ⁅x, e' m⁆)
    (hφ : ∀ x ∈ H', φ x ∈ H) (hψ : ∀ x ∈ H'', ψ x ∈ H')
    (hAd : ∀ k x, φ (Ad' k x) = Ad (f k) (φ x))
    (hAd' : ∀ k x, ψ (Ad'' k x) = Ad' (g k) (ψ x))
    (hCoeff : ∀ k m, e (ρ (f k) m) = ρ' k (e m))
    (hCoeff' : ∀ k m, e' (ρ' (g k) m) = ρ'' k (e' m)) :
    equivariantRelativeCochainComplexMap (hρ := hρ) (hρ' := hρ')
        e φ f he hφ hAd hCoeff ≫
      equivariantRelativeCochainComplexMap (hρ := hρ') (hρ' := hρ'')
        e' ψ g he' hψ hAd' hCoeff' =
      equivariantRelativeCochainComplexMap (hρ := hρ) (hρ' := hρ'')
        (e'.comp e) (φ.comp ψ) (f ∘ g) (fun x m ↦ by simp [he, he'])
        (fun x hx ↦ hφ _ (hψ x hx)) (fun k x ↦ by simp [hAd, hAd'])
        (fun k m ↦ by simp [hCoeff, hCoeff']) := by
  exact cochainSubcomplexMap_comp he he' _ _ _

end Equivariant

end TauCeti.LieModule.Cohomology
