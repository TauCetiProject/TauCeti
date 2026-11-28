/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Grauert
public import TauCeti.AlgebraicGeometry.Cohomology.Cech.FiniteProjective

/-!
# Grauert's theorem

Let `R` be a reduced Noetherian ring, `X` a quasi-compact scheme over `R` with affine diagonal (for
instance a separated one), and `M` a quasi-coherent sheaf on `X` with stalks flat over `R` whose
cohomology modules `Hⁿ(X, M)` are finitely generated, as for a coherent sheaf flat over `R` on a
proper scheme. For a prime `p` of `R`, write `X_p = X ×_R κ(p)` for the fibre and `M_p` for the
pullback of `M` to it. Fix a degree `n` and suppose that `p ↦ dim_{κ(p)} Hⁿ(X_p, M_p)` is locally
constant on `Spec R`. Then:

* `Hⁿ(X, M)` is a finite projective `R`-module, that is a locally free sheaf on `Spec R`
  (`TauCeti.AlgebraicGeometry.projective_cohomology_of_isLocallyConstant_finrank_cohomology_fiber`),
  whose rank at `p` is `dim_{κ(p)} Hⁿ(X_p, M_p)`
  (`TauCeti.AlgebraicGeometry.rankAtStalk_cohomology_eq_finrank_cohomology_fiber`);
* its formation commutes with every base change: for every `R`-algebra `R'`, with
  `Y = X ×_R R'` and projection `g : Y ⟶ X`, `Hⁿ(Y, g^* M) ≅ R' ⊗_R Hⁿ(X, M)`
  (`TauCeti.AlgebraicGeometry.nonempty_linearEquiv_tensor_cohomology_pullback`);
* so does `Hⁿ⁻¹`: `Hⁿ⁻¹(Y, g^* M) ≅ R' ⊗_R Hⁿ⁻¹(X, M)`
  (`TauCeti.AlgebraicGeometry.nonempty_linearEquiv_tensor_cohomology_pullback_of_succ`).

In particular, if `Hⁿ` vanishes on every fibre then `Hⁿ⁻¹` commutes with every base change.
For `n = 1` the module of global sections is moreover
finite projective, with rank `dim_{κ(p)} H⁰(X_p, M_p)` at `p`
(`projective_cohomology_zero_of_isLocallyConstant_finrank_cohomology_one_fiber`,
`rankAtStalk_cohomology_zero_eq_finrank_cohomology_fiber`): for a family
of curves, vanishing of `H¹` on the fibres makes `H⁰` locally free, with formation commuting with
every base change.

The proof applies the algebraic Grauert theorem for complexes
(`HomologicalComplex.projective_homology_of_isLocallyConstant` and its companions) to the bounded
complex `P` of finite projective `R`-modules computing the cohomology of every base change of `M`
(`TauCeti.AlgebraicGeometry.exists_finite_projective_complex_cohomology_pullback_of_compactSpace`).

The base change isomorphisms are stated as the existence of `R'`-linear equivalences, as in
`TauCeti.AlgebraicGeometry.exists_finite_projective_complex_cohomology_pullback`. The fibres in the
statements over all of `Spec R` are the concrete pullbacks
`pullback (X ↘ Spec R) (Spec κ(p) ⟶ Spec R)`; the base change statements accept any pullback
square.

## References

* D. Mumford, *Abelian Varieties*, §5, Corollary 2.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.12.9.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Module TensorProduct
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  (M : X.Modules) [M.IsQuasicoherent]

omit [M.IsQuasicoherent] in
/-- The fibre cohomology dimension, read on the complex `P`, is locally constant. -/
private lemma isLocallyConstant_finrank_homology_extendScalars
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hPY : ∀ (R' : Type u) [CommRing R'] [Algebra R R'] (Y : Scheme.{u}) [Y.Over (Spec (.of R'))]
      (g : Y ⟶ X), IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))) → ∀ n : ℕ,
      Nonempty ((((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
        _).obj P).homology n ≃ₗ[R'] Cohomology ((Scheme.Modules.pullback g).obj M) n))
    {n : ℕ} (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      (Cohomology ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) n)) :
    IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        _).obj P).homology (n : ℤ)) := by
  convert h using 2 with p
  obtain ⟨e⟩ := hPY p.asIdeal.ResidueField (pullback (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)))) _
    (IsPullback.of_hasPullback _ _) n
  exact e.finrank_eq

variable [IsNoetherianRing R] [IsReduced R] [CompactSpace X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  (hM : ∀ x : X, Module.Flat R (M.presheaf.stalk x))
  (hfin : ∀ n, Module.Finite R (Cohomology M n)) {n : ℕ}
  (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
    (Cohomology ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) n))

include hM hfin h

/-- **Grauert's theorem: cohomology is locally free.** Let `R` be a reduced Noetherian ring, `X`
a quasi-compact scheme over `R` with affine diagonal and `M` a quasi-coherent sheaf on `X` with
stalks flat over `R` and finitely generated cohomology. If `p ↦ dim_{κ(p)} Hⁿ(X_p, M_p)` is
locally constant on `Spec R`, then `Hⁿ(X, M)` is a projective `R`-module; it is finite by
hypothesis. -/
theorem projective_cohomology_of_isLocallyConstant_finrank_cohomology_fiber :
    Module.Projective R (Cohomology M n) := by
  obtain ⟨P, -, hP, hPX, hPY⟩ :=
    exists_finite_projective_complex_cohomology_pullback_of_compactSpace M hM hfin
  have := (hP (n - 1)).1
  have := (hP n).1
  have := (hP n).2
  have := (hP (n + 1)).1
  have := (hP (n + 1)).2
  have := Module.finitePresentation_of_projective R (P.X n)
  have := P.projective_homology_of_isLocallyConstant (CochainComplex.prev ℤ n)
    (CochainComplex.next ℤ n) (isLocallyConstant_finrank_homology_extendScalars M P hPY h)
  obtain ⟨e⟩ := hPX n
  exact Module.Projective.of_equiv e

/-- **Grauert's theorem: the rank of cohomology.** Under the hypotheses of
`projective_cohomology_of_isLocallyConstant_finrank_cohomology_fiber`, the rank of the locally
free module `Hⁿ(X, M)` at `p` is `dim_{κ(p)} Hⁿ(X_p, M_p)`. -/
theorem rankAtStalk_cohomology_eq_finrank_cohomology_fiber (p : PrimeSpectrum R) :
    rankAtStalk (Cohomology M n) p = finrank p.asIdeal.ResidueField
      (Cohomology ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) n) := by
  obtain ⟨P, -, hP, hPX, hPY⟩ :=
    exists_finite_projective_complex_cohomology_pullback_of_compactSpace M hM hfin
  have := (hP n).1
  have := (hP (n + 1)).1
  have := (hP (n + 1)).2
  obtain ⟨e⟩ := hPX n
  obtain ⟨e'⟩ := hPY p.asIdeal.ResidueField (pullback (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)))) _
    (IsPullback.of_hasPullback _ _) n
  rw [← rankAtStalk_eq_of_equiv e, ← e'.finrank_eq]
  exact P.rankAtStalk_homology_eq_finrank_fiber_homology_of_isLocallyConstant
    (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n)
    (isLocallyConstant_finrank_homology_extendScalars M P hPY h) p

/-- **Grauert's theorem: cohomology commutes with base change.** Under the hypotheses of
`projective_cohomology_of_isLocallyConstant_finrank_cohomology_fiber`, for every `R`-algebra `R'`
and every base change `Y = X ×_R R'` with projection `g : Y ⟶ X`,
`Hⁿ(Y, g^* M) ≅ R' ⊗_R Hⁿ(X, M)`. -/
theorem nonempty_linearEquiv_tensor_cohomology_pullback (R' : Type u) [CommRing R'] [Algebra R R']
    {Y : Scheme.{u}} [Y.Over (Spec (.of R'))] {g : Y ⟶ X}
    (H : IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    Nonempty (R' ⊗[R] Cohomology M n ≃ₗ[R'] Cohomology ((Scheme.Modules.pullback g).obj M) n) := by
  obtain ⟨P, -, hP, hPX, hPY⟩ :=
    exists_finite_projective_complex_cohomology_pullback_of_compactSpace M hM hfin
  have := (hP n).1
  have := (hP (n + 1)).1
  have := (hP (n + 1)).2
  obtain ⟨e⟩ := hPX n
  obtain ⟨e'⟩ := hPY R' Y g H n
  obtain ⟨e''⟩ := P.nonempty_linearEquiv_tensor_homology (CochainComplex.prev ℤ n)
    (CochainComplex.next ℤ n) (isLocallyConstant_finrank_homology_extendScalars M P hPY h) R'
  exact ⟨(LinearEquiv.baseChange R R' _ _ e).symm ≪≫ₗ e'' ≪≫ₗ e'⟩

omit h in
/-- **Grauert's theorem: the previous cohomology commutes with base change.** Let `R` be a reduced
Noetherian ring, `X` a quasi-compact scheme over `R` with affine diagonal and `M` a quasi-coherent
sheaf on `X` with stalks flat over `R` and finitely generated cohomology. If
`p ↦ dim_{κ(p)} Hⁿ⁺¹(X_p, M_p)` is locally constant on `Spec R`, then for every `R`-algebra `R'`
and every base change `Y = X ×_R R'` with projection `g : Y ⟶ X`,
`Hⁿ(Y, g^* M) ≅ R' ⊗_R Hⁿ(X, M)`. -/
theorem nonempty_linearEquiv_tensor_cohomology_pullback_of_succ
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      (Cohomology ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) (n + 1)))
    (R' : Type u) [CommRing R'] [Algebra R R'] {Y : Scheme.{u}} [Y.Over (Spec (.of R'))]
    {g : Y ⟶ X} (H : IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    Nonempty (R' ⊗[R] Cohomology M n ≃ₗ[R'] Cohomology ((Scheme.Modules.pullback g).obj M) n) := by
  obtain ⟨P, -, hP, hPX, hPY⟩ :=
    exists_finite_projective_complex_cohomology_pullback_of_compactSpace M hM hfin
  have := (hP ((n + 1 : ℕ) : ℤ)).1
  have := (hP ((n + 1 : ℕ) : ℤ)).2
  have := (hP ((n + 1 : ℕ) + 1 : ℤ)).1
  have := (hP ((n + 1 : ℕ) + 1 : ℤ)).2
  obtain ⟨e⟩ := hPX n
  obtain ⟨e'⟩ := hPY R' Y g H n
  obtain ⟨e''⟩ := P.nonempty_linearEquiv_tensor_homology_prev (i := (n : ℤ)) (by simp)
    (CochainComplex.next ℤ _) (isLocallyConstant_finrank_homology_extendScalars M P hPY h)
    (CochainComplex.prev ℤ n) (by simp) R'
  exact ⟨(LinearEquiv.baseChange R R' _ _ e).symm ≪≫ₗ e'' ≪≫ₗ e'⟩

omit h in
/-- **Grauert's theorem in degree zero: global sections are locally free.** Let `R` be a reduced
Noetherian ring, `X` a quasi-compact scheme over `R` with affine diagonal and `M` a
quasi-coherent sheaf on `X` with stalks flat over `R` and finitely generated cohomology. If
`p ↦ dim_{κ(p)} H¹(X_p, M_p)` is locally constant on `Spec R`, for instance if `H¹` vanishes on
every fibre, then `H⁰(X, M)` is a projective `R`-module; its formation commutes with every base
change by `nonempty_linearEquiv_tensor_cohomology_pullback_of_succ`. -/
theorem projective_cohomology_zero_of_isLocallyConstant_finrank_cohomology_one_fiber
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      (Cohomology ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) 1)) :
    Module.Projective R (Cohomology M 0) := by
  obtain ⟨P, hP₀, hP, hPX, hPY⟩ :=
    exists_finite_projective_complex_cohomology_pullback_of_compactSpace M hM hfin
  have := (hP 0).2
  have := (hP 1).1
  have := (hP 1).2
  have := (hP (((1 : ℕ) : ℤ) + 1)).1
  have := (hP (((1 : ℕ) : ℤ) + 1)).2
  -- The complex `P` vanishes in degree `-1`, so its homology in degree `0` is a kernel.
  have hd : P.d (-1) 0 = 0 := (P.isZero_of_isStrictlyGE 0 (-1) (by simp)).eq_of_src _ _
  have := P.flat_homology_prev_of_isLocallyConstant (i := 0) (j := ((1 : ℕ) : ℤ)) (by simp)
    (CochainComplex.next ℤ _) (isLocallyConstant_finrank_homology_extendScalars M P hPY h)
    (CochainComplex.prev ℤ 0) (by simp) hd
  obtain ⟨e⟩ := hPX 0
  have := Module.Flat.of_linearEquiv e.symm
  have := hfin 0
  have := Module.finitePresentation_of_finite R (Cohomology M 0)
  exact Module.Flat.projective_of_finitePresentation

omit h in
/-- **Grauert's theorem in degree zero: the rank of global sections.** Under the hypotheses of
`projective_cohomology_zero_of_isLocallyConstant_finrank_cohomology_one_fiber`, the rank of the
locally free module `H⁰(X, M)` at `p` is `dim_{κ(p)} H⁰(X_p, M_p)`. In particular the function
`p ↦ dim_{κ(p)} H⁰(X_p, M_p)` is locally constant. -/
theorem rankAtStalk_cohomology_zero_eq_finrank_cohomology_fiber
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      (Cohomology ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) 1))
    (p : PrimeSpectrum R) :
    rankAtStalk (Cohomology M 0) p = finrank p.asIdeal.ResidueField
      (Cohomology ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) 0) := by
  have := projective_cohomology_zero_of_isLocallyConstant_finrank_cohomology_one_fiber M hM hfin h
  have := hfin 0
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_pullback_of_succ M hM hfin (n := 0) h
    p.asIdeal.ResidueField (Y := pullback (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))
    (IsPullback.of_hasPullback _ _)
  rw [rankAtStalk_eq]
  exact e.finrank_eq

end TauCeti.AlgebraicGeometry
