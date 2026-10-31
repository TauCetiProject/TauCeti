/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.BaseChange
public import TauCeti.RingTheory.Spectrum.Prime.Semicontinuity
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Support

/-!
# Semicontinuity of first cohomology on the fibres of a two-affine cover

Let `X` be a scheme over a commutative ring `R`, covered by affine opens `U` and `V` with affine
intersection, and let `M` be a quasicoherent sheaf on `X`. For a prime `p` of `R`, write
`X_p = X ×_R κ(p)` for the fibre and `M_p` for the pullback of `M` to it. Here `H¹` is the top
cohomology, and it commutes with every base change of `R`
(`TauCeti.AlgebraicGeometry.nonempty_linearEquiv_tensor_cohomology_one_pullback`), so
`H¹(X_p, M_p) ≅ κ(p) ⊗_R H¹(X, M)`. When `H¹(X, M)` is a finite `R`-module this file deduces:

* `dim_{κ(p)} H¹(X_p, M_p)` is an upper semicontinuous function of `p ∈ Spec R`;
* `H¹(X_p, M_p) = 0` exactly when `p` lies outside the support of `H¹(X, M)`, and then `H¹`
  vanishes after base change to `R_f` for some `f ∉ p`;
* `H¹(X, M) = 0` exactly when `H¹(X_p, M_p) = 0` at every closed point `p` of `Spec R`.

Unlike the general semicontinuity theorem, these statements need no flatness of `M` or of `X`
over `R`, because top cohomology commutes with every base change. For instance, `ℙ¹_R` has such
a cover, and every quasicoherent sheaf of finite type on it has finite `H¹` over any ring
(`TauCeti.AlgebraicGeometry.projectiveLine.finite_cohomology_one`).

The fibres in the statements over all of `Spec R` are the concrete pullbacks
`pullback (X ↘ Spec R) (Spec κ(p) ⟶ Spec R)`; the pointwise statements accept any pullback
square.

## Main results

* `TauCeti.AlgebraicGeometry.finrank_cohomology_one_pullback_eq_finrank_fiber`:
  `dim_{κ(p)} H¹(X_p, M_p) = dim_{κ(p)} κ(p) ⊗_R H¹(X, M)`.
* `TauCeti.AlgebraicGeometry.subsingleton_cohomology_one_pullback_iff_notMem_support`:
  `H¹(X_p, M_p) = 0` if and only if `p ∉ Supp H¹(X, M)`.
* `TauCeti.AlgebraicGeometry.exists_notMem_subsingleton_cohomology_one_away`: vanishing of
  `H¹` on a fibre spreads to the base change to some `R_f` with `f ∉ p`.
* `TauCeti.AlgebraicGeometry.upperSemicontinuous_finrank_cohomology_one_fiber`: upper
  semicontinuity of `p ↦ dim_{κ(p)} H¹(X_p, M_p)`.
* `TauCeti.AlgebraicGeometry.subsingleton_cohomology_one_iff_forall_isMaximal`: `H¹(X, M) = 0`
  if and only if `H¹` vanishes on every closed fibre.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.12.8 and
  Theorem III.12.11.
* D. Mumford, *Abelian Varieties*, §5, Corollaries (a) and (b).
* [The Stacks Project, Lemma 0BDN](https://stacks.math.columbia.edu/tag/0BDN), semicontinuity.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Module
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  (M : X.Modules) [M.IsQuasicoherent] {U V : X.Opens} (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) (hInter : IsAffineOpen (U ⊓ V)) (hUV : U ⊔ V = ⊤)

section Fiber

variable (p : PrimeSpectrum R) {Y : Scheme.{u}} [Y.Over (Spec (.of p.asIdeal.ResidueField))]
  {g : Y ⟶ X} (H : IsPullback g (Y ↘ Spec (.of p.asIdeal.ResidueField)) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))

include hU hV hInter hUV H in
/-- On a two-affine cover with affine intersection, the dimension of `H¹` of a quasicoherent
sheaf on the fibre `Y = X ×_R κ(p)` is the dimension of the fibre `κ(p) ⊗_R H¹(X, M)` of
`H¹(X, M)` at `p`. -/
theorem finrank_cohomology_one_pullback_eq_finrank_fiber :
    finrank p.asIdeal.ResidueField (Cohomology ((Scheme.Modules.pullback g).obj M) 1) =
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (Cohomology M 1)) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_one_pullback H M hU hV hInter hUV
  exact e.finrank_eq.symm

include hU hV hInter hUV H in
/-- On a two-affine cover with affine intersection, if `H¹(X, M)` is a finite `R`-module, then
`H¹` of `M` on the fibre `Y = X ×_R κ(p)` vanishes exactly when `p` lies outside the support of
`H¹(X, M)`. -/
theorem subsingleton_cohomology_one_pullback_iff_notMem_support
    [Module.Finite R (Cohomology M 1)] :
    Subsingleton (Cohomology ((Scheme.Modules.pullback g).obj M) 1) ↔
      p ∉ Module.support R (Cohomology M 1) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_one_pullback H M hU hV hInter hUV
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    not_nontrivial_iff_subsingleton]
  exact e.toEquiv.subsingleton_congr.symm

include hU hV hInter hUV H in
/-- **Vanishing of `H¹` spreads out from a fibre.** On a two-affine cover with affine
intersection, if `H¹(X, M)` is a finite `R`-module and `H¹` of `M` vanishes on the fibre
`X ×_R κ(p)`, then there is `f ∉ p` such that `H¹` of `M` vanishes after base change to
`R_f`, that is over the basic open neighbourhood `D(f)` of `p`. -/
theorem exists_notMem_subsingleton_cohomology_one_away [Module.Finite R (Cohomology M 1)]
    (h : Subsingleton (Cohomology ((Scheme.Modules.pullback g).obj M) 1)) :
    ∃ f ∉ p.asIdeal, Subsingleton (Cohomology ((Scheme.Modules.pullback
      (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))).obj M) 1) := by
  have := Module.notMem_support_iff.mp
    ((subsingleton_cohomology_one_pullback_iff_notMem_support M hU hV hInter hUV p H).mp h)
  obtain ⟨f, hf, hsub⟩ := LocalizedModule.exists_subsingleton_away (M := Cohomology M 1) p.asIdeal
  refine ⟨f, hf, ?_⟩
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_one_pullback
    (Y := pullback (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))
    (IsPullback.of_hasPullback _ _) M hU hV hInter hUV
  -- `H¹` after base change to `R_f` is `R_f ⊗_R H¹(X, M)`, the localization of `H¹(X, M)` at `f`.
  exact (e.symm.toEquiv.trans (LocalizedModule.equivTensorProduct (Submonoid.powers f)
    (Cohomology M 1)).symm.toEquiv).subsingleton

end Fiber

include hU hV hInter hUV in
/-- **Semicontinuity of `H¹` on the fibres.** On a two-affine cover with affine intersection, if
`H¹(X, M)` is a finite `R`-module, then the dimension of `H¹` of `M` on the fibre `X ×_R κ(p)` is
an upper semicontinuous function of `p ∈ Spec R`. No flatness hypothesis is imposed on `M`. -/
theorem upperSemicontinuous_finrank_cohomology_one_fiber [Module.Finite R (Cohomology M 1)] :
    UpperSemicontinuous fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      (Cohomology ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) 1) := by
  convert Module.upperSemicontinuous_finrank_fiber (R := R) (Cohomology M 1) using 2 with p
  exact finrank_cohomology_one_pullback_eq_finrank_fiber M hU hV hInter hUV p
    (IsPullback.of_hasPullback _ _)

include hU hV hInter hUV in
/-- **`H¹` vanishes if it vanishes on the closed fibres.** On a two-affine cover with affine
intersection, if `H¹(X, M)` is a finite `R`-module, then `H¹(X, M) = 0` if and only if `H¹` of
`M` vanishes on the fibre `X ×_R κ(p)` at every maximal ideal `p` of `R`. -/
theorem subsingleton_cohomology_one_iff_forall_isMaximal [Module.Finite R (Cohomology M 1)] :
    Subsingleton (Cohomology M 1) ↔ ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal →
      Subsingleton (Cohomology ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) 1) := by
  refine Iff.trans ?_ (forall_congr' fun p ↦ imp_congr_right fun _ ↦
    (subsingleton_cohomology_one_pullback_iff_notMem_support M hU hV hInter hUV p
      (IsPullback.of_hasPullback _ _)).symm)
  rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  refine ⟨fun h p _ ↦ h p, fun h p hp ↦ ?_⟩
  -- The support is closed under specialization, so it meets the closed points if nonempty.
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  exact h ⟨m, hm.isPrime⟩ hm (Module.mem_support_mono hpm hp)

end TauCeti.AlgebraicGeometry
