/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Trivial
public import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
public import TauCeti.AlgebraicGeometry.LineBundle.SectionDegree

/-!
# Line bundles on a proper integral curve under extension of the base field

Let `X` be a proper integral curve over a field `k` and `K / k` a field extension, with
`X_K = X ×_k K`. Pulling line bundles back along `X_K ⟶ X` is injective on line-bundle classes
(`TauCeti.AlgebraicGeometry.LineBundleClass.pullback_injective`): a line bundle on `X` that
becomes trivial over `K` is already trivial over `k`.

If `L_K` is trivial then `L` has degree zero, because extending the ground field preserves
degree, and `H⁰(X, L)` has the dimension of `H⁰(X_K, 𝒪) ≠ 0` by flat base change of
cohomology, so `L` has a nonzero global section. On a proper integral curve a line bundle of
degree zero with a nonzero section is trivial.

The curve need not be smooth, geometrically integral or have a rational point, and `X_K` need not
be reduced or irreducible. Without properness the statement fails: the Picard group of the affine
real conic `x² + y² = 1` has order two, while its base change to `ℂ` is `𝔾_m`, whose Picard group
is trivial.

This is the injectivity of `Pic(X) → Pic(X_{k^s})^{Gal(k^s/k)}` for curves without rational
points, and of `Pic(X)` into the `k`-points of the relative Picard sheaf.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3 (flat base change).
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Module

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  [IsIntegral X] [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

include H in
/-- **Line-bundle classes on a proper integral curve are detected after any extension of the
base field.** For `X` a proper integral curve over `k` and `X_K = X ×_k K`, a line bundle on `X`
whose pullback to `X_K` is trivial is trivial. No smoothness, geometric integrality or rational
point is needed. -/
theorem pullback_injective : Function.Injective (pullback g) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from (X ↘ Spec (.of k))]
    infer_instance
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  suffices key : ∀ a : LineBundleClass X, pullback g a = 1 → a = 1 by
    intro a b hab
    exact mul_inv_eq_one.mp (key _ (by rw [pullback_mul, pullback_inv, hab, mul_inv_cancel]))
  intro a ha
  obtain ⟨L, rfl⟩ := mk_surjective a
  obtain ⟨e⟩ := mk_eq_one_iff.mp (by rwa [pullback_mk] at ha)
  -- `L` has degree zero, since its pullback is trivial.
  have hdeg : L.eulerDegree k = 0 := by
    rw [← eulerDegree_mk, ← eulerDegree_pullback H, ha, eulerDegree_one]
  -- `H⁰(X, L)` has the dimension of `H⁰(X_K, L_K) = H⁰(X_K, 𝒪)`, hence of `H⁰(X, 𝒪_X)`.
  have hrank : finrank k (Scheme.Modules.Cohomology L.obj 0) =
      finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0) := by
    rw [← finrank_cohomology_pullback_eq_of_isPullback H L.obj 0,
      ← finrank_cohomology_zero_trivial_eq_of_isPullback H, ← InvertibleSheaf.pullback_obj_obj,
      Scheme.Modules.finrank_cohomology_congr K
        (e ≪≫ (InvertibleSheaf.trivialObjIsoUnit Y).symm) 0]
  -- `H⁰(X, 𝒪_X)` is nonzero, so `L` has a nonzero global section.
  have : Nontrivial (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0) :=
    Module.nontrivial_of_finrank_pos (R := Γ(X, ⊤)) (by simp)
  have : Nontrivial (Scheme.Modules.Cohomology L.obj 0) :=
    Module.nontrivial_of_finrank_pos (R := k) (hrank ▸ Module.finrank_pos)
  obtain ⟨x, hx⟩ := exists_ne (0 : Scheme.Modules.Cohomology L.obj 0)
  exact (L.eulerDegree_eq_zero_iff_of_ne_zero k (Scheme.Modules.cohomologyZeroEquiv L.obj x)
    (by simpa using hx)).mp hdeg

end TauCeti.AlgebraicGeometry.LineBundleClass
