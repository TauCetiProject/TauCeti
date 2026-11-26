/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Equivalence
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.QuasiIso

/-!
# Twisted complexes are functorial in their DG coefficients

Let `m` be a twisting cocycle on a finite graded set `(P, ind)` over a DG algebra `(𝒜, d)`. Its
twisted complex `ℳ ⊗ ⟨P⟩` (`TauCeti.TwistingCocycle.twistedCochainComplex`) is defined for every
DG right module `(ℳ, dM)`. A morphism `f : ℳ → 𝒩` of DG right modules, applied to every
coefficient, gives a morphism of twisted complexes `ℳ ⊗ ⟨P⟩ → 𝒩 ⊗ ⟨P⟩`
(`TauCeti.TwistingCocycle.twistedCochainComplexMap`): it preserves total degrees, and it commutes
with the twisted differential `D(α ⊗ x) = dα ⊗ x + (-1)^{|α|} Σ_y α · m(x, y) ⊗ y` because `f`
commutes with the differentials, preserves degrees and is right linear over the algebra. This is
functorial (`TauCeti.TwistingCocycle.twistedCochainComplexMap_id`,
`TauCeti.TwistingCocycle.twistedCochainComplexMap_comp`), and it commutes with the continuation
maps of continuation cocycles, which act on the generators only
(`TauCeti.ContinuationCocycle.continuationHom_twistedCochainComplexMap`).

**A quasi-isomorphism of coefficients induces a quasi-isomorphism of twisted complexes**
(`TauCeti.TwistingCocycle.quasiIso_twistedCochainComplexMap`). On a finite set every function is
finitely supported, and the equivalence `(P → M) ≃ (P →₀ M)` identifies the twisted complex with
the coefficient complex of the row-finite form `TauCeti.TwistingCocycle.toRowFinite` of the
cocycle (`TauCeti.TwistingCocycle.twistedCochainComplexIsoToRowFinite`), naturally in the
coefficients. A twisting cocycle is one-sided by definition, `m x y = 0` whenever
`ind x ≤ ind y`, and on a finite set its indices are bounded below, so it is semi-free: the
relation saying that `y` occurs in the row of `x` is well-founded
(`TauCeti.RowFiniteTwistingCocycle.wellFounded_mem_support`). The row-finite theorem
`TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientCochainComplexMap` then concludes. So the
homology of a twisted complex depends on its DG coefficient module only up to quasi-isomorphism.

For the DG Morse complexes of Barraud, Damian, Humilière and Oancea this is the naturality of DG
Morse homology in the coefficients and its invariance under quasi-isomorphisms of DG local
systems; see `TauCeti.Geometry.Manifold.Morse.DG.Coefficients`.

## Main definitions

* `TauCeti.TwistingCocycle.twistedCochainComplexMap`: the morphism of twisted complexes induced
  by a morphism of DG right modules.
* `TauCeti.TwistingCocycle.twistedCochainComplexIsoToRowFinite`: the isomorphism of the twisted
  complex with the coefficient complex of the row-finite form of the cocycle.

## Main results

* `TauCeti.TwistingCocycle.twistedCochainComplexMap_id`,
  `TauCeti.TwistingCocycle.twistedCochainComplexMap_comp`: functoriality.
* `TauCeti.ContinuationCocycle.continuationHom_twistedCochainComplexMap`: naturality of
  continuation maps in the coefficients.
* `TauCeti.TwistingCocycle.quasiIso_twistedCochainComplexMap`: quasi-isomorphisms of coefficients
  induce quasi-isomorphisms of twisted complexes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3–4.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M N K : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  [AddCommGroup K] [Module R K] [Module Aᵐᵒᵖ K] [IsScalarTower R Aᵐᵒᵖ K]
  {P Q : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} [Fintype P] [Fintype Q]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {𝒩 : ℤ → Submodule R N} [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece 𝒩]
  {𝒦 : ℤ → Submodule R K} [DirectSum.Decomposition 𝒦]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece 𝒦]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dK : K →ₗ[R] K}
  (hM : IsDGRightModule h ℳ dM) (hN : IsDGRightModule h 𝒩 dN) (hK : IsDGRightModule h 𝒦 dK)

namespace DGRightModuleHom

variable {hM hN}

omit [Fintype P] in
/-- A morphism of DG right modules, applied to every coefficient, preserves the total degree of
`P → M`. -/
theorem compLeft_mem_twistedTotalGrading (f : DGRightModuleHom hM hN) {n : ℤ} {g : P → M}
    (hg : g ∈ twistedTotalGrading ℳ ind n) :
    LinearMap.compLeft (f.toLinearMap.restrictScalars R) P g ∈ twistedTotalGrading 𝒩 ind n := by
  rw [mem_twistedTotalGrading_iff] at hg ⊢
  exact fun x ↦ f.map_mem' (hg x)

/-- A morphism of DG right modules, applied to every coefficient, commutes with the twisted
differentials of any matrix `m`. -/
theorem compLeft_twistedDifferential (f : DGRightModuleHom hM hN) (m : P → P → A) (g : P → M) :
    LinearMap.compLeft (f.toLinearMap.restrictScalars R) P (twistedDifferential m ℳ dM g) =
      twistedDifferential m 𝒩 dN (LinearMap.compLeft (f.toLinearMap.restrictScalars R) P g) := by
  funext y
  simp only [LinearMap.compLeft_apply, Function.comp_apply, twistedDifferential_apply,
    LinearMap.coe_restrictScalars, coe_toLinearMap, map_add, map_sum, map_d, map_koszulTwist,
    LinearMapClass.map_smul]

omit [Fintype Q] in
/-- A morphism of DG right modules, applied to every coefficient, commutes with the continuation
map of any matrix. -/
theorem compLeft_continuationMap (f : DGRightModuleHom hM hN) (ν : P → Q → A) (g : P → M) :
    LinearMap.compLeft (f.toLinearMap.restrictScalars R) Q (continuationMap R M ν g) =
      continuationMap R N ν (LinearMap.compLeft (f.toLinearMap.restrictScalars R) P g) := by
  funext y
  simp only [LinearMap.compLeft_apply, Function.comp_apply, continuationMap_apply,
    LinearMap.coe_restrictScalars, coe_toLinearMap, map_sum, LinearMapClass.map_smul]

end DGRightModuleHom

namespace TwistingCocycle

variable (m : TwistingCocycle 𝒜 d P ind)

/-- **The morphism of twisted complexes induced by a morphism of DG coefficients**: a morphism
`f : ℳ → 𝒩` of DG right modules, applied to every coefficient, as a morphism of twisted complexes
`ℳ ⊗ ⟨P⟩ → 𝒩 ⊗ ⟨P⟩`. -/
noncomputable def twistedCochainComplexMap (f : DGRightModuleHom hM hN) :
    m.twistedCochainComplex dM hM ⟶ m.twistedCochainComplex dN hN where
  f n := ModuleCat.ofHom
    ((twistedCochainComplexXEquiv m.mem_graded m.twisting hN n).symm.toLinearMap ∘ₗ
      (LinearMap.compLeft (f.toLinearMap.restrictScalars R) P).restrict
        (fun _ hg ↦ f.compLeft_mem_twistedTotalGrading hg) ∘ₗ
      (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n).toLinearMap)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    refine (twistedCochainComplexXEquiv m.mem_graded m.twisting hN (i + 1)).injective
      (Subtype.ext ?_)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      twistedCochainComplexXEquiv_d, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearMap.restrict_apply]
    exact (f.compLeft_twistedDifferential m.m _).symm

/-- In the identifications of the complex terms with the total-degree pieces of `P → M` and
`P → N`, the morphism induced by `f` applies `f` to every coefficient. -/
@[simp]
theorem twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply (f : DGRightModuleHom hM hN)
    (n : ℤ) (x : (m.twistedCochainComplex dM hM).X n) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting hN n
        (((m.twistedCochainComplexMap hM hN f).f n).hom x) : P → N) =
      f ∘ (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n x : P → M) := by
  funext y
  simp [twistedCochainComplexMap]

/-- Two morphisms into a twisted complex agree when they agree on the underlying functions. -/
theorem twistedCochainComplex_hom_ext {C : CochainComplex (ModuleCat.{max uP uM} R) ℤ}
    {φ ψ : C ⟶ m.twistedCochainComplex dN hN}
    (hφψ : ∀ n (x : C.X n),
      (twistedCochainComplexXEquiv m.mem_graded m.twisting hN n ((φ.f n).hom x) : P → N) =
        twistedCochainComplexXEquiv m.mem_graded m.twisting hN n ((ψ.f n).hom x)) :
    φ = ψ := by
  ext n x
  exact (twistedCochainComplexXEquiv m.mem_graded m.twisting hN n).injective
    (Subtype.ext (hφψ n x))

/-- The identity of a DG right module induces the identity of its twisted complex. -/
@[simp]
theorem twistedCochainComplexMap_id :
    m.twistedCochainComplexMap hM hM (DGRightModuleHom.id hM) = 𝟙 _ :=
  m.twistedCochainComplex_hom_ext hM fun n x ↦ by
    simp only [twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply,
      DGRightModuleHom.coe_id, Function.id_comp, HomologicalComplex.id_f, ModuleCat.hom_id,
      LinearMap.id_apply]

/-- The composite of morphisms of DG right modules induces the composite of the morphisms of
twisted complexes. -/
@[simp]
theorem twistedCochainComplexMap_comp (f : DGRightModuleHom hM hN) (g : DGRightModuleHom hN hK) :
    m.twistedCochainComplexMap hM hK (g.comp f) =
      m.twistedCochainComplexMap hM hN f ≫ m.twistedCochainComplexMap hN hK g :=
  m.twistedCochainComplex_hom_ext hK fun n x ↦ by
    simp only [twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply,
      DGRightModuleHom.coe_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, Function.comp_assoc]

/-! ### The row-finite twisted complex -/

/-- **The twisted complex is the row-finite twisted complex**: on a finite set every function is
finitely supported, and the equivalence `(P → M) ≃ (P →₀ M)` is an isomorphism from the twisted
complex of a twisting cocycle to the coefficient complex of its row-finite form, since it
intertwines the two differentials
(`TauCeti.RowFiniteTwistingCocycle.linearEquivFunOnFinite_coefficientDifferential`). -/
noncomputable def twistedCochainComplexIsoToRowFinite :
    m.twistedCochainComplex dM hM ≅ m.toRowFinite.coefficientCochainComplex hM :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ LinearEquiv.toModuleIso
      (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n ≪≫ₗ
        ((Finsupp.linearEquivFunOnFinite R M P).ofSubmodules _ (twistedTotalGrading ℳ ind n) <| by
          ext g
          rw [Submodule.mem_map_equiv, mem_rowFiniteTotalGrading_iff_twistedTotalGrading,
            LinearEquiv.apply_symm_apply]).symm ≪≫ₗ
        (m.toRowFinite.coefficientCochainComplexXEquiv hM n).symm))
    (by
      rintro i j rfl
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      refine (m.toRowFinite.coefficientCochainComplexXEquiv hM (i + 1)).injective
        (Subtype.ext ((Finsupp.linearEquivFunOnFinite R M P).injective ?_))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
        ModuleCat.hom_ofHom, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply, RowFiniteTwistingCocycle.coefficientCochainComplexXEquiv_d,
        RowFiniteTwistingCocycle.linearEquivFunOnFinite_coefficientDifferential,
        twistedCochainComplexXEquiv_d, LinearEquiv.ofSubmodules_symm_apply, toRowFinite_m])

/-- Under the identifications of the complex terms with coefficient vectors, the isomorphism
`TauCeti.TwistingCocycle.twistedCochainComplexIsoToRowFinite` is the finite-support/function
equivalence. -/
@[simp]
theorem coefficientCochainComplexXEquiv_twistedCochainComplexIsoToRowFinite_hom_f_apply (n : ℤ)
    (x : (m.twistedCochainComplex dM hM).X n) :
    (m.toRowFinite.coefficientCochainComplexXEquiv hM n
        (((m.twistedCochainComplexIsoToRowFinite hM).hom.f n).hom x) : P →₀ M) =
      (Finsupp.linearEquivFunOnFinite R M P).symm
        (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n x) := by
  simp [twistedCochainComplexIsoToRowFinite, LinearEquiv.ofSubmodules_symm_apply]

/-- Under the identifications of the complex terms with coefficient vectors, the inverse of the
isomorphism `TauCeti.TwistingCocycle.twistedCochainComplexIsoToRowFinite` is the
function/finite-support equivalence. -/
@[simp]
theorem twistedCochainComplexXEquiv_twistedCochainComplexIsoToRowFinite_inv_f_apply (n : ℤ)
    (x : (m.toRowFinite.coefficientCochainComplex hM).X n) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n
        (((m.twistedCochainComplexIsoToRowFinite hM).inv.f n).hom x) : P → M) =
      Finsupp.linearEquivFunOnFinite R M P
        (m.toRowFinite.coefficientCochainComplexXEquiv hM n x) := by
  simp [twistedCochainComplexIsoToRowFinite, LinearEquiv.ofSubmodules_apply]

/-- The isomorphism with the row-finite twisted complex is natural in the coefficients: it carries
the morphism of twisted complexes induced by a morphism of DG right modules to the coefficient map
of the row-finite complexes. -/
@[reassoc]
theorem twistedCochainComplexIsoToRowFinite_hom_coefficientCochainComplexMap
    (f : DGRightModuleHom hM hN) :
    (m.twistedCochainComplexIsoToRowFinite hM).hom ≫
        m.toRowFinite.coefficientCochainComplexMap hM hN f =
      m.twistedCochainComplexMap hM hN f ≫ (m.twistedCochainComplexIsoToRowFinite hN).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  refine (m.toRowFinite.coefficientCochainComplexXEquiv hN n).injective (Subtype.ext ?_)
  ext y
  simp

/-! ### Quasi-isomorphism invariance -/

/-- **Quasi-isomorphism invariance of twisted complexes.** A quasi-isomorphism `f : ℳ → 𝒩` of DG
right modules induces a quasi-isomorphism `ℳ ⊗ ⟨P⟩ → 𝒩 ⊗ ⟨P⟩` of the twisted complexes of a
twisting cocycle on a finite set. Such a cocycle is one-sided with indices bounded below, hence
semi-free, and the row-finite theorem
`TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientCochainComplexMap` applies. -/
theorem quasiIso_twistedCochainComplexMap {f : DGRightModuleHom hM hN} (hf : f.IsQuasiIso) :
    QuasiIso (m.twistedCochainComplexMap hM hN f) := by
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℤ, ∀ x, p₀ ≤ ind x :=
    (Set.finite_range ind).bddBelow.imp fun _ h x ↦ h ⟨x, rfl⟩
  have hrf := m.toRowFinite.quasiIso_coefficientCochainComplexMap hM hN
    (m.toRowFinite.wellFounded_mem_support (fun x y hxy ↦ by simpa using m.one_sided x y hxy)
      hp₀) hf
  exact (quasiIso_iff_of_arrow_mk_iso (m.twistedCochainComplexMap hM hN f)
    (m.toRowFinite.coefficientCochainComplexMap hM hN f)
    (Arrow.isoMk (m.twistedCochainComplexIsoToRowFinite hM)
      (m.twistedCochainComplexIsoToRowFinite hN)
      (m.twistedCochainComplexIsoToRowFinite_hom_coefficientCochainComplexMap hM hN f))).mpr hrf

end TwistingCocycle

/-! ### Naturality of continuation maps -/

namespace ContinuationCocycle

variable {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}

/-- **Continuation maps are natural in the coefficients**: the continuation map of a continuation
cocycle `ν`, which acts on the generators, commutes with the morphism of twisted complexes induced
by a morphism of DG right modules, which acts on the coefficients. -/
@[reassoc]
theorem continuationHom_twistedCochainComplexMap (ν : ContinuationCocycle mP mQ)
    (f : DGRightModuleHom hM hN) :
    ν.continuationHom hM ≫ mQ.twistedCochainComplexMap hM hN f =
      mP.twistedCochainComplexMap hM hN f ≫ ν.continuationHom hN :=
  mQ.twistedCochainComplex_hom_ext hN fun n x ↦ by
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      TwistingCocycle.twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply,
      continuationHom_f_apply]
    exact f.compLeft_continuationMap ν.ν _

end ContinuationCocycle

end TauCeti
