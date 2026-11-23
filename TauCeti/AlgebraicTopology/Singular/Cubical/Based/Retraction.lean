/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Deformation
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic

/-!
# The retraction of cubical chains onto based chains

Let `D` be a `TauCeti.BasedCubeDeformation n x`: a homotopy of every singular cube `c` of `X` to
an `n`-based cube, compatible with faces and degeneracies. As for every deformation of the singular
cubes (`TauCeti.CubeDeformation`), the end of the homotopy induces a chain endomorphism
`D.endChainMap R` of Massey's normalized cubical chains, and the swept-cube operator is a chain
homotopy `D.endHomotopy R` from the identity to it. This file records what is special to based
cubes.

* The end of the homotopy of `c` is the `n`-based cube `D.endCube c`, and `D` fixes the cubes that
  are already `n`-based. So the image of `D.endChainMap R` is spanned by `n`-based cubes: it is a
  retraction of the normalized cubical chains onto them.
* In a dimension `m` with `0 < m < n`, the only `n`-based `m`-cube is the constant cube at `x`,
  which is degenerate, so the retraction vanishes. As it induces the identity on homology, the
  normalized cubical homology of `X` vanishes in these degrees. By the comparison of cubical and
  simplicial singular chains, so does the singular homology of `X`: **the singular homology of an
  `(n - 1)`-connected space vanishes in the positive degrees below `n`**
  (`TauCeti.isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup`).

In degree `n` the retraction lands in the span of the `n`-based `n`-cubes, which are the
generalized loops of `Ω^ (Fin n) X x`; this is where the identification of the `n`-th homology with
the homotopy group through the Hurewicz map starts.

## Main results

* `TauCeti.BasedCubeDeformation.isBased_endCube`: the deformation of every cube ends at an
  `n`-based cube.
* `TauCeti.BasedCubeDeformation.endChain_mem_span`: the retraction lands in the span of the
  `n`-based cubes.
* `TauCeti.BasedCubeDeformation.endChain_eq_zero`: the retraction vanishes in the positive
  dimensions below `n`.
* `TauCeti.isZero_homology_normalizedCubicalChainComplex_of_subsingleton_homotopyGroup`,
  `TauCeti.isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup`: the vanishing of the
  normalized cubical and of the singular homology of an `(n - 1)`-connected space in the positive
  degrees below `n`.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407–447, for the
  deformation of singular chains of an `(n - 1)`-connected space into the subcomplex of simplices
  sending the `(n - 1)`-skeleton to the base point.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II, for normalized
  cubical chains.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology unitInterval

namespace TauCeti

namespace BasedCubeDeformation

section Cubes

variable {X : Type*} [TopologicalSpace X] {n : ℕ} {x : X} (D : BasedCubeDeformation n x)

/-- The deformation of every cube ends at an `n`-based cube. -/
theorem isBased_endCube {m : ℕ} (c : SingularCube X m) : (D.endCube c).IsBased n x := by
  have h : D.endCube c = (D.homotopy c).curry 1 := by
    ext y
    simp
  exact h ▸ D.isBased_curry_one c

/-- The deformation fixes the `n`-based cubes. -/
theorem endCube_of_isBased {m : ℕ} {c : SingularCube X m} (hc : c.IsBased n x) :
    D.endCube c = c := by
  ext y
  simp [hc]

/-- In a dimension below `n`, every cube retracts to the constant cube at `x`. -/
theorem endCube_eq_const {m : ℕ} (hm : m < n) (c : SingularCube X m) :
    D.endCube c = ContinuousMap.const _ x := by
  ext y
  exact (SingularCube.isBased_iff_of_lt hm).1 (D.isBased_endCube c) y

variable (R : Type*) [Ring R]

/-- The retraction lands in the span of the `n`-based cubes. -/
theorem endChain_mem_span {m : ℕ} (g : NormalizedCubicalChain X R m) :
    D.endChain R m g ∈ Submodule.span R
      (NormalizedCubicalChain.ofCube X R '' {c | c.IsBased n x}) := by
  induction g using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add a b ha hb => simpa using Submodule.add_mem _ ha hb
  | smul r a ha => simpa using Submodule.smul_mem _ r ha
  | ofCube c =>
    rw [CubeDeformation.endChain_ofCube]
    exact Submodule.subset_span ⟨_, D.isBased_endCube c, rfl⟩

/-- **The retraction vanishes in the positive dimensions below `n`**: there, every cube retracts
to the constant cube at `x`, which is degenerate. -/
theorem endChain_eq_zero {m : ℕ} (hm : m + 1 < n) : D.endChain R (m + 1) = 0 := by
  refine NormalizedCubicalChain.linearMap_ext fun c ↦ ?_
  rw [CubeDeformation.endChain_ofCube, D.endCube_eq_const hm, LinearMap.zero_apply]
  exact NormalizedCubicalChain.ofCube_eq_zero R
    (SingularCube.isDegenerate_iff.2 ⟨0, SingularCube.isDegenerateAt_iff.2 fun _ _ ↦ rfl⟩)

end Cubes

end BasedCubeDeformation

universe u

/-- **The normalized cubical homology of an `(n - 1)`-connected space vanishes in the positive
degrees below `n`.** The retraction onto `n`-based cubes induces the identity on homology, since it
is chain homotopic to the identity, and it vanishes in these degrees. -/
theorem isZero_homology_normalizedCubicalChainComplex_of_subsingleton_homotopyGroup
    {X : TopCat.{u}} {n : ℕ} {x : X} (hX : ∀ k < n, Subsingleton (HomotopyGroup (Fin k) X x))
    (R : Type u) [Ring R] {m : ℕ} (hm0 : m ≠ 0) (hm : m < n) :
    IsZero (((normalizedCubicalChainComplex R).obj X).homology m) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  set D := basedCubeDeformation hX
  have hρ : (D.endChainMap R).f (m + 1) = 0 := by
    ext g
    exact (D.endChainMap_f_apply R (m + 1) g).trans
      (LinearMap.congr_fun (D.endChain_eq_zero R hm) g)
  have hcycles : HomologicalComplex.cyclesMap (D.endChainMap R) (m + 1) = 0 := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ (m + 1)), HomologicalComplex.cyclesMap_i,
      hρ, comp_zero, zero_comp]
  rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.homologyMap_id,
    (D.endHomotopy R).homologyMap_eq, ← cancel_epi (HomologicalComplex.homologyπ _ (m + 1)),
    HomologicalComplex.homologyπ_naturality, hcycles, zero_comp, comp_zero]

/-- **The singular homology of an `(n - 1)`-connected space vanishes in the positive degrees below
`n`.** If `π_k(X, x)` is trivial for every `k < n` (for `k = 0`, if `X` is path connected), then
`H_m(X; R) = 0` for `0 < m < n`, for every coefficient ring `R`. -/
theorem isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup {X : TopCat.{u}} {n : ℕ}
    {x : X} (hX : ∀ k < n, Subsingleton (HomotopyGroup (Fin k) X x)) (R : Type u) [Ring R]
    {m : ℕ} (hm0 : m ≠ 0) (hm : m < n) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).obj X) :=
  (isZero_homology_normalizedCubicalChainComplex_of_subsingleton_homotopyGroup hX R hm0
    hm).of_iso (singularCubicalHomologyIso R X m)

end TauCeti
