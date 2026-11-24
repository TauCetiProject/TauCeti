/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Equivalence
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.QuasiIso
public import TauCeti.Algebra.Homology.ShortComplex.Colimit

/-!
# Twisted complexes over the path components of a space

On a space `B` that need not be path connected, a DG local system is a family `(𝓕_c)` indexed by
the path components `c` of `B`, with `𝓕_c` a right DG module over the chain algebra
`C_*(Ω_{b_c} B)` of the Moore loops at a chosen basepoint `b_c` of `c`
(`TauCeti.DGLocalSystemFamily`). A Morse function or a Hamiltonian on such a space has its
generators in the different components, and its trajectories never leave a component, so its
twisting data is a family as well: for each component `c`, a graded set of generators `P_c` and a
row-finite twisting cocycle `m_c` with values in `C_*(Ω_{b_c} B)`. The free loop space `𝓛Q` of a
manifold, whose path components are the free homotopy classes of loops, is the main example.

The twisted complex of such data is the direct sum over the components of the row-finite twisted
complexes `𝓕_c ⊗ ⟨P_c⟩`, here the coproduct of cochain complexes
(`TauCeti.DGLocalSystemFamily.twistedComplex`). This file develops its basic theory from the
corresponding facts for a single component.

* It is functorial in the coefficient family (`TauCeti.DGLocalSystemFamily.twistedComplexFunctor`).
* Since coproducts of modules are exact, its homology is the direct sum of the homologies of the
  summands (`TauCeti.DGLocalSystemFamily.twistedComplexHomologyIso`).
* A morphism of coefficient families induces a quasi-isomorphism exactly when it does so on every
  component (`TauCeti.DGLocalSystemFamily.quasiIso_twistedComplexMap_iff`). For semi-free cocycles,
  such as one-sided cocycles with indices bounded below, a componentwise quasi-isomorphism of
  coefficients therefore gives a quasi-isomorphism of twisted complexes
  (`TauCeti.DGLocalSystemFamily.quasiIso_twistedComplexMap`).
* Families of continuation cocycles induce morphisms of twisted complexes, compatibly with
  identities and composition (`TauCeti.DGLocalSystemFamily.twistedComplexContinuation`), and
  families of homologous cocycles induce quasi-isomorphisms
  (`TauCeti.DGLocalSystemFamily.quasiIso_twistedComplexContinuation`).
* On a path-connected space the twisted complex is that of the single component
  (`TauCeti.DGLocalSystemFamily.isIso_twistedComplexι`).

## Implementation notes

The generators `P_c` live in the universe of the coefficient modules, so that all the twisted
complexes are complexes of modules in one universe. The existence and exactness of the coproducts
indexed by the path components are instance arguments; for modules they are supplied by
`TauCeti.Algebra.Category.ModuleCat.AB` when the path components are small enough.

## Main definitions

* `TauCeti.DGLocalSystemFamily.twistedComplex m 𝓕`: the twisted complex `⨁_c 𝓕_c ⊗ ⟨P_c⟩`.
* `TauCeti.DGLocalSystemFamily.twistedComplexι m 𝓕 c`: the inclusion of the summand of `c`.
* `TauCeti.DGLocalSystemFamily.twistedComplexFunctor m`: functoriality in the coefficients.
* `TauCeti.DGLocalSystemFamily.twistedComplexHomologyIso m 𝓕 n`: the homology is the direct sum
  of the homologies of the summands.
* `TauCeti.DGLocalSystemFamily.twistedComplexContinuation ν 𝓕`: the morphism induced by a family
  of continuation cocycles.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3, 4 and 13.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

namespace DGLocalSystemFamily

universe uB uR uM

variable {B : Type uB} [TopologicalSpace B] {β : PathComponentBasepoints B}
  {R : Type uR} [CommRing R]
  {P : ZerothHomotopy B → Type uM} {ind : ∀ c, P c → ℤ}
  (m : ∀ c, RowFiniteTwistingCocycle (R := R) (A := loopChainAlgebra B (β.point c) R)
    (cubicalChainGrading (MooreLoopSpace B (β.point c)) R)
    (cubicalChainDifferential (MooreLoopSpace B (β.point c)) R) (P c) (ind c))
  [HasColimitsOfShape (Discrete (ZerothHomotopy B)) (ModuleCat.{uM} R)]

/-! ### The twisted complex and its functoriality -/

/-- **The twisted complex of a DG local system on a space with chosen basepoints**: the direct sum
over the path components `c` of the row-finite twisted complexes `𝓕_c ⊗ ⟨P_c⟩` of the twisting
cocycles `m_c` with values in `C_*(Ω_{b_c} B)`. -/
abbrev twistedComplex (𝓕 : DGLocalSystemFamily.{uM} β R) :
    CochainComplex (ModuleCat.{uM} R) ℤ :=
  ∐ fun c ↦ (m c).coefficientCochainComplex (𝓕 c).isDGRightModule

/-- The inclusion of the twisted complex `𝓕_c ⊗ ⟨P_c⟩` of the path component `c` into the
twisted complex of the family. -/
def twistedComplexι (𝓕 : DGLocalSystemFamily.{uM} β R) (c : ZerothHomotopy B) :
    (m c).coefficientCochainComplex (𝓕 c).isDGRightModule ⟶ twistedComplex m 𝓕 :=
  Sigma.ι (fun c ↦ (m c).coefficientCochainComplex (𝓕 c).isDGRightModule) c

theorem twistedComplexι_def (𝓕 : DGLocalSystemFamily.{uM} β R) (c : ZerothHomotopy B) :
    twistedComplexι m 𝓕 c =
      Sigma.ι (fun c ↦ (m c).coefficientCochainComplex (𝓕 c).isDGRightModule) c :=
  (rfl)

/-- A morphism out of the twisted complex of a family, given by its restrictions to the summands
of the path components, restricts on the summand of `c` to the given map. -/
@[reassoc (attr := simp)]
theorem twistedComplexι_desc (𝓕 : DGLocalSystemFamily.{uM} β R)
    {K : CochainComplex (ModuleCat.{uM} R) ℤ}
    (f : ∀ c, (m c).coefficientCochainComplex (𝓕 c).isDGRightModule ⟶ K) (c : ZerothHomotopy B) :
    twistedComplexι m 𝓕 c ≫ Sigma.desc f = f c :=
  Sigma.ι_comp_desc f c

/-- Morphisms out of the twisted complex of a family are determined by their restrictions to the
summands of the path components. -/
theorem twistedComplex_hom_ext {𝓕 : DGLocalSystemFamily.{uM} β R}
    {K : CochainComplex (ModuleCat.{uM} R) ℤ} {f g : twistedComplex m 𝓕 ⟶ K}
    (h : ∀ c, twistedComplexι m 𝓕 c ≫ f = twistedComplexι m 𝓕 c ≫ g) : f = g :=
  Sigma.hom_ext _ _ h

/-- The morphism of twisted complexes induced by a morphism of coefficient families: on the
summand of each path component `c`, the coefficient map of `φ_c`. -/
def twistedComplexMap {𝓕 𝓖 : DGLocalSystemFamily.{uM} β R} (φ : 𝓕 ⟶ 𝓖) :
    twistedComplex m 𝓕 ⟶ twistedComplex m 𝓖 :=
  Limits.Sigma.map fun c ↦ (m c).coefficientCochainComplexMap _ _ (φ c)

@[reassoc (attr := simp)]
theorem twistedComplexι_twistedComplexMap {𝓕 𝓖 : DGLocalSystemFamily.{uM} β R} (φ : 𝓕 ⟶ 𝓖)
    (c : ZerothHomotopy B) :
    twistedComplexι m 𝓕 c ≫ twistedComplexMap m φ =
      (m c).coefficientCochainComplexMap _ _ (φ c) ≫ twistedComplexι m 𝓖 c :=
  Sigma.ι_map _ c

@[simp]
theorem twistedComplexMap_id (𝓕 : DGLocalSystemFamily.{uM} β R) :
    twistedComplexMap m (𝟙 𝓕) = 𝟙 (twistedComplex m 𝓕) := by
  refine twistedComplex_hom_ext m fun c ↦ ?_
  simp [DGRightModuleCat.id_eq_id, RowFiniteTwistingCocycle.coefficientCochainComplexMap_id]

@[reassoc, simp]
theorem twistedComplexMap_comp {𝓕 𝓖 𝓗 : DGLocalSystemFamily.{uM} β R} (φ : 𝓕 ⟶ 𝓖)
    (ψ : 𝓖 ⟶ 𝓗) :
    twistedComplexMap m (φ ≫ ψ) = twistedComplexMap m φ ≫ twistedComplexMap m ψ := by
  refine twistedComplex_hom_ext m fun c ↦ ?_
  simp [DGRightModuleCat.comp_eq_comp, RowFiniteTwistingCocycle.coefficientCochainComplexMap_comp]

/-- The twisted complex as a functor of the coefficient family. -/
@[expose] def twistedComplexFunctor :
    DGLocalSystemFamily.{uM} β R ⥤ CochainComplex (ModuleCat.{uM} R) ℤ where
  obj := twistedComplex m
  map := twistedComplexMap m
  map_id := twistedComplexMap_id m
  map_comp := twistedComplexMap_comp m

@[simp]
theorem twistedComplexFunctor_obj (𝓕 : DGLocalSystemFamily.{uM} β R) :
    (twistedComplexFunctor m).obj 𝓕 = twistedComplex m 𝓕 :=
  (rfl)

@[simp]
theorem twistedComplexFunctor_map {𝓕 𝓖 : DGLocalSystemFamily.{uM} β R} (φ : 𝓕 ⟶ 𝓖) :
    (twistedComplexFunctor m).map φ = twistedComplexMap m φ :=
  (rfl)

/-! ### Homology and quasi-isomorphisms -/

section Homology

variable [HasExactColimitsOfShape (Discrete (ZerothHomotopy B)) (ModuleCat.{uM} R)]

/-- **The homology of the twisted complex of a family is the direct sum of the homologies of the
summands**, those of the twisted complexes `𝓕_c ⊗ ⟨P_c⟩` of the path components. -/
def twistedComplexHomologyIso (𝓕 : DGLocalSystemFamily.{uM} β R) (n : ℤ) :
    (twistedComplex m 𝓕).homology n ≅
      ∐ fun c ↦ ((m c).coefficientCochainComplex (𝓕 c).isDGRightModule).homology n :=
  (asIso (sigmaComparison (HomologicalComplex.homologyFunctor _ _ n)
    fun c ↦ (m c).coefficientCochainComplex (𝓕 c).isDGRightModule)).symm

/-- Under `twistedComplexHomologyIso`, the map induced on homology by the inclusion of the summand
of `c` is the inclusion of the homology of that summand. -/
@[reassoc (attr := simp)]
theorem homologyMap_twistedComplexι_twistedComplexHomologyIso_hom
    (𝓕 : DGLocalSystemFamily.{uM} β R) (c : ZerothHomotopy B) (n : ℤ) :
    HomologicalComplex.homologyMap (twistedComplexι m 𝓕 c) n ≫
        (twistedComplexHomologyIso m 𝓕 n).hom =
      Sigma.ι (fun c ↦ ((m c).coefficientCochainComplex (𝓕 c).isDGRightModule).homology n) c := by
  rw [twistedComplexHomologyIso, Iso.symm_hom, asIso_inv]
  exact map_ι_comp_inv_sigmaComparison (HomologicalComplex.homologyFunctor _ _ n)
    (fun c ↦ (m c).coefficientCochainComplex (𝓕 c).isDGRightModule) c

/-- Under `twistedComplexHomologyIso`, the inclusion of the homology of the summand of `c` is the
map induced on homology by the inclusion of that summand. -/
@[reassoc (attr := simp)]
theorem ι_twistedComplexHomologyIso_inv (𝓕 : DGLocalSystemFamily.{uM} β R)
    (c : ZerothHomotopy B) (n : ℤ) :
    Sigma.ι (fun c ↦ ((m c).coefficientCochainComplex (𝓕 c).isDGRightModule).homology n) c ≫
        (twistedComplexHomologyIso m 𝓕 n).inv =
      HomologicalComplex.homologyMap (twistedComplexι m 𝓕 c) n := by
  rw [Iso.comp_inv_eq, homologyMap_twistedComplexι_twistedComplexHomologyIso_hom]

/-- The identification of the homology of the twisted complex with the direct sum of the
homologies of the summands is natural in the coefficient family. -/
@[reassoc]
theorem twistedComplexHomologyIso_hom_naturality {𝓕 𝓖 : DGLocalSystemFamily.{uM} β R}
    (φ : 𝓕 ⟶ 𝓖) (n : ℤ) :
    HomologicalComplex.homologyMap (twistedComplexMap m φ) n ≫
        (twistedComplexHomologyIso m 𝓖 n).hom =
      (twistedComplexHomologyIso m 𝓕 n).hom ≫
        Limits.Sigma.map fun c ↦
          HomologicalComplex.homologyMap ((m c).coefficientCochainComplexMap _ _ (φ c)) n := by
  rw [← Iso.inv_comp_eq, ← Category.assoc]
  refine Sigma.hom_ext _ _ fun c ↦ ?_
  rw [Category.assoc, ι_twistedComplexHomologyIso_inv_assoc,
    ← HomologicalComplex.homologyMap_comp_assoc]
  simp [HomologicalComplex.homologyMap_comp]

/-- **Quasi-isomorphisms of coefficient families.** A morphism of coefficient families induces a
quasi-isomorphism of twisted complexes exactly when it induces one on the twisted complex of every
path component. -/
theorem quasiIso_twistedComplexMap_iff {𝓕 𝓖 : DGLocalSystemFamily.{uM} β R} (φ : 𝓕 ⟶ 𝓖) :
    QuasiIso (twistedComplexMap m φ) ↔
      ∀ c, QuasiIso ((m c).coefficientCochainComplexMap _ _ (φ c)) := by
  simp only [quasiIso_iff]
  exact ⟨fun h c n ↦ (quasiIsoAt_sigmaMap_iff _).mp (h n) c,
    fun h n ↦ (quasiIsoAt_sigmaMap_iff _).mpr fun c ↦ h c n⟩

/-- **Quasi-isomorphism invariance of twisted complexes over the path components.** If every
cocycle `m_c` is semi-free, its row relation being well-founded, then a morphism of coefficient
families which is a quasi-isomorphism of DG modules on every path component induces a
quasi-isomorphism of twisted complexes. -/
theorem quasiIso_twistedComplexMap
    (hwf : ∀ c, WellFounded fun y x ↦ y ∈ ((m c).m x).support)
    {𝓕 𝓖 : DGLocalSystemFamily.{uM} β R} {φ : 𝓕 ⟶ 𝓖} (hφ : ∀ c, (φ c).IsQuasiIso) :
    QuasiIso (twistedComplexMap m φ) :=
  (quasiIso_twistedComplexMap_iff m φ).mpr fun c ↦
    (m c).quasiIso_coefficientCochainComplexMap _ _ (hwf c) (hφ c)

end Homology

/-! ### Continuation maps -/

section Continuation

variable {Q S : ZerothHomotopy B → Type uM} {indQ : ∀ c, Q c → ℤ} {indS : ∀ c, S c → ℤ}
  {m' : ∀ c, RowFiniteTwistingCocycle (R := R) (A := loopChainAlgebra B (β.point c) R)
    (cubicalChainGrading (MooreLoopSpace B (β.point c)) R)
    (cubicalChainDifferential (MooreLoopSpace B (β.point c)) R) (Q c) (indQ c)}
  {m'' : ∀ c, RowFiniteTwistingCocycle (R := R) (A := loopChainAlgebra B (β.point c) R)
    (cubicalChainGrading (MooreLoopSpace B (β.point c)) R)
    (cubicalChainDifferential (MooreLoopSpace B (β.point c)) R) (S c) (indS c)}

variable {m} in
/-- The morphism of twisted complexes induced by a family of continuation cocycles
`ν_c : m_c → m'_c`: on the summand of each path component `c`, the continuation map of `ν_c`. -/
def twistedComplexContinuation (ν : ∀ c, RowFiniteContinuationCocycle (m c) (m' c))
    (𝓕 : DGLocalSystemFamily.{uM} β R) :
    twistedComplex m 𝓕 ⟶ twistedComplex m' 𝓕 :=
  Limits.Sigma.map fun c ↦ (ν c).continuationHom (𝓕 c).isDGRightModule

variable {m} in
@[reassoc (attr := simp)]
theorem twistedComplexι_twistedComplexContinuation
    (ν : ∀ c, RowFiniteContinuationCocycle (m c) (m' c)) (𝓕 : DGLocalSystemFamily.{uM} β R)
    (c : ZerothHomotopy B) :
    twistedComplexι m 𝓕 c ≫ twistedComplexContinuation ν 𝓕 =
      (ν c).continuationHom (𝓕 c).isDGRightModule ≫ twistedComplexι m' 𝓕 c :=
  Sigma.ι_map _ c

/-- The identity continuation cocycles induce the identity of the twisted complex. -/
@[simp]
theorem twistedComplexContinuation_refl (𝓕 : DGLocalSystemFamily.{uM} β R) :
    twistedComplexContinuation
        (fun c ↦ RowFiniteContinuationCocycle.refl (m c) (loopChain_isDGAlgebra B (β.point c) R))
        𝓕 =
      𝟙 (twistedComplex m 𝓕) := by
  refine twistedComplex_hom_ext m fun c ↦ ?_
  simp

variable {m} in
/-- The composite of two families of continuation cocycles induces the composite of the morphisms
of twisted complexes. -/
@[reassoc, simp]
theorem twistedComplexContinuation_comp (ν : ∀ c, RowFiniteContinuationCocycle (m c) (m' c))
    (μ : ∀ c, RowFiniteContinuationCocycle (m' c) (m'' c)) (𝓕 : DGLocalSystemFamily.{uM} β R) :
    twistedComplexContinuation
        (fun c ↦ (ν c).comp (μ c) (loopChain_isDGAlgebra B (β.point c) R)) 𝓕 =
      twistedComplexContinuation ν 𝓕 ≫ twistedComplexContinuation μ 𝓕 := by
  refine twistedComplex_hom_ext m fun c ↦ ?_
  simp [RowFiniteContinuationCocycle.continuationHom_comp]

variable [HasExactColimitsOfShape (Discrete (ZerothHomotopy B)) (ModuleCat.{uM} R)]

variable {m} in
/-- **Homologous cocycles give quasi-isomorphic twisted complexes.** If on every path component
the cocycles `m_c` and `m'_c` are homologous, then the continuation map of the family is a
quasi-isomorphism, whatever the coefficient family. -/
theorem quasiIso_twistedComplexContinuation
    (H : ∀ c, RowFiniteHomologous (loopChain_isDGAlgebra B (β.point c) R) (m c) (m' c))
    (𝓕 : DGLocalSystemFamily.{uM} β R) :
    QuasiIso (twistedComplexContinuation (fun c ↦ (H c).ν) 𝓕) := by
  rw [quasiIso_iff]
  refine fun n ↦ (quasiIsoAt_sigmaMap_iff _).mpr fun c ↦ ?_
  rw [← RowFiniteHomologous.homotopyEquiv_hom (H c) (𝓕 c).isDGRightModule]
  infer_instance

end Continuation

/-! ### Path-connected spaces -/

/-- **The connected case.** On a path-connected space the twisted complex of a family is the
twisted complex of its single path component: the inclusion of that summand is an isomorphism. -/
theorem isIso_twistedComplexι [Subsingleton (ZerothHomotopy B)]
    (𝓕 : DGLocalSystemFamily.{uM} β R) (c : ZerothHomotopy B) :
    IsIso (twistedComplexι m 𝓕 c) := by
  have : Unique (ZerothHomotopy B) := uniqueOfSubsingleton c
  obtain rfl := Subsingleton.elim c default
  rw [twistedComplexι_def, ← coproductUniqueIso_inv]
  infer_instance

end DGLocalSystemFamily

end TauCeti
