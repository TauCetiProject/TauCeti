/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.TopColumn
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Category.ModuleCat.Range

/-!
# The top column of the index spectral sequence of a twisted complex

Let `m` be a twisting cocycle on a finite set `P` of generators whose indices are all at most
`q + 1`. The twisted differential never raises the index, and every twisting term strictly lowers
it, so restricting a family `P → M` to the generators of the top index `q + 1` is a cochain map
from the twisted complex `ℳ ⊗ ⟨P⟩` to the twisted complex `ℳ ⊗ ⟨P_{q+1}⟩` of the zero cocycle on
those generators (`TauCeti.TwistingCocycle.topIndexRestriction`): on a cycle it reads off the
components at the generators of top index, each of which is a cycle of `ℳ`.

The restriction kills exactly the classes coming from the generators of index at most `q`
(`TauCeti.TwistingCocycle.homologyMap_topIndexRestriction_eq_zero_iff`), which is also the kernel
of the projection of the cohomology onto the top column `E∞` of the index spectral sequence. So
a class has nonzero restriction to the generators of top index exactly when it is detected on the
top column of the limit page
(`TauCeti.TwistingCocycle.indexToTopColumnEInfty_eq_zero_iff`), and the top column of the limit
page embeds into the cohomology of `ℳ ⊗ ⟨P_{q+1}⟩`, the top column of the first page
(`TauCeti.TwistingCocycle.indexTopColumnEInftyToHomology`).

As motivation: for the twisted complex of a Morse function with a unique maximum `x_max` of
index `n`, the restriction is the projection onto the coefficients of `x_max`, which the reference
uses to compute the shriek map of the inclusion of a point. The results here supply the algebraic
input to its characterization of the classes living over the fundamental class of the base, by
their component at the maximum (Proposition 2.5 of the reference) and by the top column
`E^∞_{n,*}` of the spectral sequence (Proposition 2.6). This file involves no Morse function,
shriek map or fundamental class, and does not prove the identification of the restriction with
the shriek map.

## Main definitions

* `TauCeti.TwistingCocycle.topIndexRestriction`: restriction to the generators of top index, a
  cochain map from the twisted complex.
* `TauCeti.TwistingCocycle.indexToTopColumnEInfty`: the projection of the cohomology of the twisted
  complex onto the top column of the limit page of the index spectral sequence.
* `TauCeti.TwistingCocycle.indexTopColumnEInftyToHomology`: the embedding of that top column into
  the cohomology of the generators of top index.

## Main results

* `TauCeti.TwistingCocycle.homologyMap_topIndexRestriction_eq_zero_iff`: a class restricts to zero
  on the generators of top index exactly when it comes from the generators of lower index.
* `TauCeti.TwistingCocycle.indexToTopColumnEInfty_eq_zero_iff`: a class is detected on the top
  column of the limit page exactly when its restriction to the generators of top index is nonzero.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Propositions 2.5 and 2.6.
-/

public section

open CategoryTheory Limits MulOpposite HomologicalComplex

universe uR uA uM uP

namespace TauCeti.TwistingCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ}
  [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (m : TwistingCocycle 𝒜 d P ind) (hM : IsDGRightModule h ℳ dM) {q : ℤ}
  (hq : ∀ x, ind x ≤ q + 1)

/-! ### Restriction to the generators of top index -/

include hq in
/-- **Restriction to the generators of top index.** When every generator has index at most
`q + 1`, restricting a family `P → M` to the generators of index `q + 1` is a cochain map from the
twisted complex `ℳ ⊗ ⟨P⟩` to the twisted complex `ℳ ⊗ ⟨P_{q+1}⟩` of the zero cocycle on those
generators: no twisting term ends at a generator of top index. It is the projection
`twistedIndexCochainComplexProj` of the last stage `F_{q+1}` of the index filtration, which is the
whole twisted complex, onto its graded piece. -/
noncomputable def topIndexRestriction :
    m.twistedCochainComplex dM hM ⟶
      (0 : TwistingCocycle 𝒜 d {x // ind x = q + 1} fun x ↦ ind x).twistedCochainComplex dM hM :=
  haveI := m.isIso_twistedIndexCochainComplexι hM hq
  inv (m.twistedIndexCochainComplexι hM (q + 1)) ≫ m.twistedIndexCochainComplexProj dM hM (q + 1)

/-- On the last stage `F_{q+1}` of the index filtration, which is the whole twisted complex,
`topIndexRestriction` is the restriction `twistedIndexCochainComplexProj` onto the graded piece
of index `q + 1`. -/
@[reassoc (attr := simp)]
theorem twistedIndexCochainComplexι_comp_topIndexRestriction :
    m.twistedIndexCochainComplexι hM (q + 1) ≫ m.topIndexRestriction dM hM hq =
      m.twistedIndexCochainComplexProj dM hM (q + 1) := by
  have := m.isIso_twistedIndexCochainComplexι hM hq
  rw [topIndexRestriction, IsIso.hom_inv_id_assoc]

/-- In each degree, `topIndexRestriction` restricts a family to the generators of top index. -/
@[simp]
theorem topIndexRestriction_f_apply (n : ℤ) (f : (m.twistedCochainComplex dM hM).X n) :
    (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM n
        (((m.topIndexRestriction dM hM hq).f n).hom f) : {x // ind x = q + 1} → M) =
      LinearMap.funLeft R M Subtype.val
        (twistedCochainComplexXEquiv m.mem_graded m.twisting hM n f) := by
  have := m.isIso_twistedIndexCochainComplexι hM hq
  -- Write `f` as the image of a family `g` of the last stage `F_{q+1}` of the index filtration.
  obtain ⟨g, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((m.twistedIndexCochainComplexι hM (q + 1)).f n)) f
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f,
    twistedIndexCochainComplexι_comp_topIndexRestriction, twistedIndexCochainComplexProj_f_apply,
    twistedIndexCochainComplexι_apply]

/-- **The kernel of the restriction to the generators of top index.** A cohomology class of the
twisted complex restricts to zero on the generators of top index `q + 1` exactly when it comes
from the subcomplex `F_q` spanned by the generators of index at most `q`. -/
theorem homologyMap_topIndexRestriction_eq_zero_iff {k : ℤ}
    (α : (m.twistedCochainComplex dM hM).homology k) :
    (homologyMap (m.topIndexRestriction dM hM hq) k).hom α = 0 ↔
      α ∈ LinearMap.range (homologyMap (m.twistedIndexCochainComplexι hM q) k).hom := by
  have := m.isIso_twistedIndexCochainComplexι hM hq
  set ι := m.twistedIndexCochainComplexι hM (q + 1)
  set e := homologyMapIso (asIso ι) k
  -- Through the isomorphism `ι : F_{q+1} ⟶ ℳ ⊗ ⟨P⟩`, the restriction is the projection of
  -- `F_{q+1}` onto its graded piece, whose kernel on cohomology is the image of `H^k(F_q)` by the
  -- long exact sequence of `F_q ⟶ F_{q+1} ⟶ ℳ ⊗ ⟨P_{q+1}⟩`.
  have hS := m.twistedIndexShortComplex_shortExact dM hM q
  rw [twistedIndexShortComplex_def] at hS
  have hr : m.topIndexRestriction dM hM hq =
      inv ι ≫ m.twistedIndexCochainComplexProj dM hM (q + 1) := by
    rw [IsIso.eq_inv_comp, twistedIndexCochainComplexι_comp_topIndexRestriction]
  set j := homologyMap (m.twistedIndexCochainComplexMap hM (Int.le_add_one le_rfl)) k
  have hinv : homologyMap (inv ι) k = e.inv := by simp [e]
  have hj : homologyMap (m.twistedIndexCochainComplexι hM q) k = j ≫ e.hom := by
    simp [e, ι, j, ← homologyMap_comp]
  rw [hr, homologyMap_comp, hinv, ModuleCat.hom_comp, LinearMap.comp_apply, ← LinearMap.mem_ker,
    ← (hS.homology_exact₂ k).moduleCat_range_eq_ker, hj, ModuleCat.mem_range_comp_iso_hom]

/-! ### The top column of the index spectral sequence -/

/-- **The projection onto the top column of the index spectral sequence.** When every generator
has index at most `q + 1`, the cohomology of the twisted complex is the last piece of the
filtration of the abutment of the index spectral sequence, and this is its projection onto the
limit object `E∞` at `q`, the top column of the limit page. -/
noncomputable abbrev indexToTopColumnEInfty (k : ℤ) :
    (m.twistedCochainComplex dM hM).homology k ⟶
      (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
        (m.twistedIndexSubobject hM) (m.twistedIndexSubobject_mono hM))).EInfty q k :=
  CochainComplex.filtrationToTopColumnEInfty _ _ (m.twistedIndexSubobject_eq_top hM hq) k

/-- **Classes detected on the top column.** A cohomology class of the twisted complex vanishes on
the top column of the limit page of the index spectral sequence exactly when its restriction to
the generators of top index vanishes in cohomology. -/
theorem indexToTopColumnEInfty_eq_zero_iff {k : ℤ}
    (α : (m.twistedCochainComplex dM hM).homology k) :
    (m.indexToTopColumnEInfty dM hM hq k).hom α = 0 ↔
      (homologyMap (m.topIndexRestriction dM hM hq) k).hom α = 0 := by
  rw [CochainComplex.filtrationToTopColumnEInfty_eq_zero_iff,
    homologyMap_topIndexRestriction_eq_zero_iff, m.twistedIndexSubobject_eq_mk hM q,
    ← Subobject.underlyingIso_hom_comp_eq_mk, homologyMap_comp, ModuleCat.hom_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _
      ((ModuleCat.epi_iff_surjective _).1 inferInstance))]

/-- **The top column of the limit page embeds in the top column of the first page.** The
restriction to the generators of top index factors through the projection onto the top column of
the limit page of the index spectral sequence, by a monomorphism into the cohomology of the twisted
complex `ℳ ⊗ ⟨P_{q+1}⟩` of the generators of top index. -/
noncomputable def indexTopColumnEInftyToHomology (k : ℤ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor
        (m.twistedIndexSubobject hM) (m.twistedIndexSubobject_mono hM))).EInfty q k ⟶
      ((0 : TwistingCocycle 𝒜 d {x // ind x = q + 1} fun x ↦ ind x).twistedCochainComplex dM
        hM).homology k :=
  Abelian.epiDesc (m.indexToTopColumnEInfty dM hM hq k)
    (homologyMap (m.topIndexRestriction dM hM hq) k) <| by
      ext x
      have hx := congrArg (fun f ↦ f.hom x) (kernel.condition (m.indexToTopColumnEInfty dM hM hq k))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at hx ⊢
      exact (m.indexToTopColumnEInfty_eq_zero_iff dM hM hq _).1 hx

/-- The projection onto the top column of the limit page, followed by its embedding in the
cohomology of the generators of top index, is the restriction to those generators. -/
@[reassoc (attr := simp)]
theorem indexToTopColumnEInfty_comp_indexTopColumnEInftyToHomology (k : ℤ) :
    m.indexToTopColumnEInfty dM hM hq k ≫ m.indexTopColumnEInftyToHomology dM hM hq k =
      homologyMap (m.topIndexRestriction dM hM hq) k :=
  Abelian.comp_epiDesc _ _ _

instance (k : ℤ) : Mono (m.indexTopColumnEInftyToHomology dM hM hq k) := by
  refine (ModuleCat.mono_iff_injective _).2 <| (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨α, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (m.indexToTopColumnEInfty dM hM hq k)) x
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    indexToTopColumnEInfty_comp_indexTopColumnEInftyToHomology] at hx
  exact (m.indexToTopColumnEInfty_eq_zero_iff dM hM hq α).2 hx

end TauCeti.TwistingCocycle
