/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Homology.Embedding.CochainComplex
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
public import TauCeti.Algebra.Homology.ModuleCat.FiniteFreeResolution
public import TauCeti.Algebra.Homology.ModuleCat.FlatCycles
import TauCeti.RingTheory.Flat.Pi

/-!
# Base change of bounded complexes of flat modules

Let `f : R →+* S` be a homomorphism of commutative rings. Extension of scalars along `f` is only
right exact, but it preserves the exactness of complexes of flat modules that are bounded above:
the cycles of such an acyclic complex are flat, so it is spliced from short exact sequences with
flat third terms, and these remain short exact after extension of scalars. Consequently, a
quasi-isomorphism between bounded-above complexes of flat `R`-modules remains a
quasi-isomorphism after extension of scalars to any `S`, since its mapping cone is again a
bounded-above acyclic complex of flat modules.

The main result is the lemma of Mumford and Grothendieck on cohomology and base change, in its
algebraic form. Let `R` be a Noetherian ring and `K` a complex of flat `R`-modules concentrated in
degrees `[a, b]` whose cohomology is finitely generated. Then there are a complex `P` of finitely
generated projective `R`-modules, also concentrated in degrees `[a, b]`, and a
quasi-isomorphism `P ⟶ K` which remains a quasi-isomorphism after extension of scalars along every
`R →+* S`. Thus the cohomology of every base change `S ⊗_R K` is computed by the complex
`S ⊗_R P` of finite projective `S`-modules. For a scheme `X` proper over `R` with a finite affine
cover and a coherent sheaf on `X` flat over `R`, the alternating Čech complex of the sheaf is a
bounded complex of flat modules with finitely generated cohomology which computes the cohomology of
every base change of the sheaf, so it is such a `K`.

Following Mumford, `P` is the canonical truncation in degrees `≥ a` of a complex `L` of finite free
modules with a quasi-isomorphism `L ⟶ K`, which exists by
`CochainComplex.exists_quasiIso_finite_free`. In degrees `> a` the terms of `P` are those of `L`; in
degree `a` the term is the quotient `L.opcycles a` of `L.X a`, which is finitely generated. It is
flat because it is the bottom term of a quasi-isomorphism `P ⟶ K` between bounded complexes whose
other terms are flat (`CochainComplex.flat_X_of_quasiIso`), hence projective.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.map_extendScalars`: extension of scalars preserves
  short exact sequences whose third term is flat.
* `CochainComplex.acyclic_mapHomologicalComplex_extendScalars`: extension of scalars preserves
  the acyclicity of bounded-above complexes of flat modules.
* `CochainComplex.quasiIso_mapHomologicalComplex_extendScalars_map`: extension of scalars
  preserves quasi-isomorphisms between bounded-above complexes of flat modules.
* `CochainComplex.flat_X_of_quasiIso`: the bottom term of a complex quasi-isomorphic to a bounded
  complex of flat modules is flat if its other terms are.
* `CochainComplex.exists_quasiIso_finite_projective`: a bounded complex of flat modules over a
  Noetherian ring with finitely generated cohomology is quasi-isomorphic, compatibly with every
  base change, to a bounded complex of finite projective modules with the same bounds.

## References

* D. Mumford, *Abelian Varieties*, Tata Institute, 1970, §5, the lemma on cohomology and base
  change and its proof.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, §III.12, Lemma 12.3.
-/

public section

open CategoryTheory Limits HomologicalComplex

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)

namespace CategoryTheory.ShortComplex.ShortExact

/-- **Extension of scalars preserves short exact sequences with flat third term.** If
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is a short exact sequence of `R`-modules and `X₃` is flat, then
`0 ⟶ S ⊗ X₁ ⟶ S ⊗ X₂ ⟶ S ⊗ X₃ ⟶ 0` is short exact for every `f : R →+* S`. -/
theorem map_extendScalars {X : ShortComplex (ModuleCat.{u} R)} (hX : X.ShortExact)
    [Module.Flat R X.X₃] : (X.map (ModuleCat.extendScalars f)).ShortExact := by
  -- By definition of `ModuleCat.extendScalars`, the images of `X.f` and `X.g` are the maps
  -- `S ⊗ X₁ ⟶ S ⊗ X₂ ⟶ S ⊗ X₃` induced by `X.f` and `X.g` on the right factor.
  let Q := (ModuleCat.restrictScalars f).obj (ModuleCat.of S S)
  have hg := (ModuleCat.epi_iff_surjective _).1 hX.epi_g
  have hfg := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hX.exact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact lTensor_exact Q hfg hg
  · rw [ModuleCat.mono_iff_injective]
    exact LinearMap.lTensor_injective_of_exact_of_flat X.g.hom hg X.f.hom
      hX.moduleCat_injective_f hfg Q
  · rw [ModuleCat.epi_iff_surjective]
    exact LinearMap.lTensor_surjective Q hg

end CategoryTheory.ShortComplex.ShortExact

namespace CochainComplex

/-- **Extension of scalars preserves acyclic bounded-above complexes of flat modules.** If `E` is
an acyclic complex of flat `R`-modules which is bounded above, then `S ⊗_R E` is acyclic for every
`f : R →+* S`. -/
theorem acyclic_mapHomologicalComplex_extendScalars (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) [E.IsStrictlyLE n] (hflat : ∀ i, Module.Flat R (E.X i)) (hE : E.Acyclic) :
    (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E).Acyclic := by
  let F := ModuleCat.extendScalars f
  -- The image under `F` of each cycle sequence `Zⱼ ⟶ Eⱼ ⟶ Zⱼ₊₁` is short exact, because the
  -- cycles of the acyclic flat complex `E` are flat.
  have hS (j : ℤ) : ((ShortComplex.mk (E.iCycles j) (E.toCycles j (j + 1))
      (E.iCycles_toCycles j (j + 1))).map F).ShortExact := by
    have : Module.Flat R (E.cycles (j + 1)) := E.flat_cycles_of_exactAt_of_isStrictlyLE n (j + 1)
      (fun k _ ↦ hflat k) (fun k _ ↦ hE k)
    have h := E.cyclesShortComplex_shortExact j (j + 1) (by simp) (hE _)
    rw [cyclesShortComplex_def] at h
    exact h.map_extendScalars f
  intro i
  rw [exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
  have := epi_toCycles_of_exactAt (hE i) (i := i - 1) (by simp)
  -- Compare the image of `Eᵢ₋₁ ⟶ Eᵢ ⟶ Eᵢ₊₁` with that of the cycle sequence in degree `i`, through
  -- the image of `Eᵢ₋₁ ⟶ Eᵢ ⟶ Zᵢ₊₁`: the image of `Eᵢ₋₁ ⟶ Zᵢ` is an epimorphism, and the image of
  -- the inclusion `Zᵢ₊₁ ⟶ Eᵢ₊₁` is a monomorphism by short exactness in degree `i + 1`.
  let T := ShortComplex.mk (F.map (E.d (i - 1) i)) (F.map (E.toCycles i (i + 1)))
    (by rw [← F.map_comp, ← E.toCycles_i (i - 1) i, Category.assoc, iCycles_toCycles,
      comp_zero, F.map_zero])
  let φ : T ⟶ (ShortComplex.mk (E.iCycles i) (E.toCycles i (i + 1))
      (E.iCycles_toCycles i (i + 1))).map F :=
    { τ₁ := F.map (E.toCycles (i - 1) i), τ₂ := 𝟙 _, τ₃ := 𝟙 _
      comm₁₂ := by simp [T, ← F.map_comp] }
  let ψ : T ⟶ ((F.mapHomologicalComplex (.up ℤ)).obj E).sc' (i - 1) i (i + 1) :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := F.map (E.iCycles (i + 1))
      comm₂₃ := by simp [T, ← F.map_comp] }
  -- `F` preserves epimorphisms, as tensor products are right exact.
  have : Epi φ.τ₁ := (ModuleCat.epi_iff_surjective _).2
    (LinearMap.lTensor_surjective ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))
      ((ModuleCat.epi_iff_surjective _).1 inferInstance))
  have : Mono ψ.τ₃ := (hS (i + 1)).mono_f
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).1
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (hS i).exact)

/-- The mapping cone of a morphism `φ : K ⟶ L` of complexes of modules is flat in degree `i` when
`K.X (i + 1)` and `L.X i` are flat. -/
lemma flat_mappingCone_X {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) (i : ℤ)
    [Module.Flat R (K.X (i + 1))] [Module.Flat R (L.X i)] :
    Module.Flat R ((mappingCone φ).X i) :=
  Module.Flat.of_linearEquiv ((homotopyCofiber.XIsoBiprod φ i (i + 1) rfl) ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv

/-- **Extension of scalars preserves quasi-isomorphisms of bounded-above flat complexes.** A
quasi-isomorphism `φ : K ⟶ L` between bounded-above complexes of flat `R`-modules induces a
quasi-isomorphism `S ⊗_R K ⟶ S ⊗_R L` for every `f : R →+* S`. -/
theorem quasiIso_mapHomologicalComplex_extendScalars_map
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) [QuasiIso φ] (n : ℤ)
    [K.IsStrictlyLE n] [L.IsStrictlyLE n] (hK : ∀ i, Module.Flat R (K.X i))
    (hL : ∀ i, Module.Flat R (L.X i)) :
    QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map φ) := by
  have := isStrictlyLE_mappingCone φ n n n
  have hFD := acyclic_mapHomologicalComplex_extendScalars f (mappingCone φ) n
    (fun i ↦ have := hK (i + 1); have := hL i; flat_mappingCone_X φ i)
    ((quasiIso_iff_acyclic_mappingCone φ).1 inferInstance)
  rw [quasiIso_iff_acyclic_mappingCone]
  exact fun i ↦ (hFD i).of_iso (mappingCone.mapHomologicalComplexIso φ _)

/-- **Flatness of the bottom term of a quasi-isomorphism of bounded flat complexes.** Let
`ψ : P ⟶ K` be a quasi-isomorphism of bounded-above complexes of modules concentrated in degrees
`≥ a`. If `K` is flat and `P` is flat in degrees `> a`, then `P` is flat in degree `a` as well. -/
theorem flat_X_of_quasiIso {P K : CochainComplex (ModuleCat.{u} R) ℤ} (ψ : P ⟶ K) [QuasiIso ψ]
    (a n : ℤ) [P.IsStrictlyGE a] [K.IsStrictlyGE a] [P.IsStrictlyLE n] [K.IsStrictlyLE n]
    (hP : ∀ i, a < i → Module.Flat R (P.X i)) (hK : ∀ i, Module.Flat R (K.X i)) :
    Module.Flat R (P.X a) := by
  let D := mappingCone ψ
  have := isStrictlyLE_mappingCone ψ n n n
  have hflat (j : ℤ) (hj : a - 1 < j) : Module.Flat R (D.X j) :=
    have := hP (j + 1) (by lia)
    have := hK j
    flat_mappingCone_X ψ j
  -- The cone is acyclic and flat in degrees `≥ a`, so its opcycles in degree `a - 1` are flat; as
  -- the cone vanishes in degree `a - 2`, these opcycles are its term in degree `a - 1`.
  have := D.flat_opcycles_of_exactAt_of_isStrictlyLE n (a - 1) hflat
    (fun j _ ↦ (quasiIso_iff_acyclic_mappingCone ψ).1 inferInstance j)
  have hzero : IsZero (D.X (a - 2)) := (mappingCone.isZero_X_iff ψ _).2
    ⟨P.isZero_of_isStrictlyGE a _, K.isZero_of_isStrictlyGE a _⟩
  have hD : Module.Flat R (D.X (a - 1)) := Module.Flat.of_linearEquiv
    (D.pOpcyclesIso (a - 2) (a - 1) (by simp; lia) (hzero.eq_of_src _ _)).toLinearEquiv
  -- The term `P.X a` of the source is a direct summand of the cone in degree `a - 1`.
  exact Module.Flat.of_retract (f := hD) ((mappingCone.inl ψ).v a (a - 1) (by lia)).hom
    ((mappingCone.fst ψ).1.v (a - 1) a (by lia)).hom
    (by rw [← ModuleCat.hom_comp, mappingCone.inl_v_fst_v, ModuleCat.hom_id])

/-- **Finite projective models of bounded flat complexes** (Mumford). Let `R` be a Noetherian ring
and `K` a complex of flat `R`-modules concentrated in degrees `[a, b]` whose cohomology is finitely
generated. Then there is a quasi-isomorphism `ψ : P ⟶ K` from a complex `P` of finitely generated
projective `R`-modules, also concentrated in degrees `[a, b]`, which remains a quasi-isomorphism
after extension of scalars along every `f : R →+* S`. In particular the cohomology of every base
change `S ⊗_R K` is that of `S ⊗_R P`. -/
theorem exists_quasiIso_finite_projective [IsNoetherianRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hflat : ∀ i, Module.Flat R (K.X i)) (hK : ∀ i, Module.Finite R (K.homology i)) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (ψ : P ⟶ K), P.IsStrictlyGE a ∧
      P.IsStrictlyLE b ∧ (∀ i, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) ∧
      QuasiIso ψ ∧ ∀ (S : Type v) [CommRing S] (f : R →+* S),
        QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map ψ) := by
  obtain ⟨L, g, _, _, hL⟩ := exists_quasiIso_finite_free K b hK
  let P := L.truncGE a
  let ψ : P ⟶ K := truncGEMap g a ≫ inv (K.πTruncGE a)
  have : QuasiIso (truncGEMap g a) := (quasiIso_truncGEMap_iff g a).2 fun i _ ↦ inferInstance
  -- Above degree `a`, the truncation agrees with the finite free complex `L`.
  have hfree (i : ℤ) (hi : a < i) : Module.Free R (P.X i) ∧ Module.Finite R (P.X i) :=
    have := (hL i).1
    have := (hL i).2
    let e := (L.truncGEXIso a i).toLinearEquiv
    ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
  have hproj (i : ℤ) : Module.Finite R (P.X i) ∧ Module.Projective R (P.X i) := by
    rcases lt_trichotomy a i with h | rfl | h
    · obtain ⟨_, _⟩ := hfree i h
      exact ⟨inferInstance, inferInstance⟩
    · -- In degree `a` the truncation is the quotient `L.opcycles a` of the finite module `L.X a`,
      -- and it is flat because `ψ` is a quasi-isomorphism of bounded complexes.
      have := (hL a).2
      have : Module.Finite R (P.X a) := Module.Finite.of_surjective
        (L.pOpcycles a ≫ (L.truncGEXIsoOpcycles a).inv).hom
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      have : Module.Flat R (P.X a) :=
        flat_X_of_quasiIso ψ a b (fun i hi ↦ have := (hfree i hi).1; inferInstance) hflat
      have := Module.finitePresentation_of_finite R (P.X a)
      exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩
    · have := ModuleCat.subsingleton_of_isZero (P.isZero_of_isStrictlyGE a i)
      exact ⟨inferInstance, inferInstance⟩
  refine ⟨P, ψ, inferInstance, inferInstance, hproj, inferInstance,
    fun S _ f ↦ quasiIso_mapHomologicalComplex_extendScalars_map f ψ b
      (fun i ↦ have := (hproj i).2; inferInstance) hflat⟩

end CochainComplex
