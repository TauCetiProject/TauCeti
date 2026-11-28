/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.AddCircle
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Sphere
public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Basic
public import TauCeti.Topology.ComplexProjectiveSpace.Sphere2

/-!
# The fundamental class of the total space of the Hopf fibration lives over the base

For the Hopf fibration `S¹ → S²ⁿ⁺¹ → CPⁿ` (`TauCeti.ComplexProjectiveSpace.mk`), the shriek map of
the inclusion of a point `b` of `CPⁿ` sends the fundamental class of `S²ⁿ⁺¹` to the fundamental
class of the fibre circle over `b`. In the notation of Barraud, Damian, Humilière and Oancea,
`j_![S²ⁿ⁺¹] = [S¹]`, and `[S²ⁿ⁺¹]` lives over the fundamental class of `CPⁿ` at every point. For
`n = 1` this is the statement that `[S³]` lives over `[S²]` for the Hopf map `S³ → S²`.

The shriek map `j_! : H₂ₙ₊₁(S²ⁿ⁺¹) → H₁(F)` of a point `b` in the affine open `{X_k ≠ 0}` of `CPⁿ`
(`TauCeti.ComplexProjectiveSpace.hopfShriek`) is the localization at the fibre `F` over `b`,
followed by the identification `H₂ₙ₊₁(S²ⁿ⁺¹, S²ⁿ⁺¹ ∖ F) ≅ H₁(F)` read in the affine chart at `k`
(`TauCeti.TopCat.singularHomologyComplFiberIso`). Since the Hopf fibration is trivial over that
affine open (`TauCeti.ComplexProjectiveSpace.hopfTrivialization`), `j_!` sends fundamental classes
to fundamental classes
(`TauCeti.IsFundamentalClass.singularHomologyComplFiberIso_hom_fiberLocalization`).

The fibre over `[v]` is the orbit circle `{u • v}`, parametrized by `t ↦ e^{2πit} v` on `ℝ / ℤ`
(`TauCeti.ComplexProjectiveSpace.hopfFiberCircleHomeomorph`), and the image of the circuit class
of `ℝ / ℤ` is its class `[S¹]` (`TauCeti.ComplexProjectiveSpace.hopfFiberClass`). With integral
coefficients, a fundamental class of a circle is `±` its circuit class, so `j_!` sends a
fundamental class of `S²ⁿ⁺¹` to `±[S¹]`; the sign depends on the orientation conventions, which
`TauCeti.IsFundamentalClass` leaves free.

## Main definitions

* `TauCeti.ComplexProjectiveSpace.hopfShriek`: the shriek map of a point of `CPⁿ` for the Hopf
  fibration.
* `TauCeti.ComplexProjectiveSpace.hopfFiberClass`: the integral class of the fibre circle.

## Main results

* `TauCeti.IsFundamentalClass.hopfShriek`: the shriek map sends a fundamental class of `S²ⁿ⁺¹` to a
  fundamental class of the fibre.
* `TauCeti.IsFundamentalClass.hopfShriek_eq_or_eq_neg_hopfFiberClass`: with integral coefficients,
  it sends it to `±[S¹]`.
* `TauCeti.IsFundamentalClass.livesOverFundamentalClass_hopfHom`: a fundamental class of `S²ⁿ⁺¹`
  lives over the fundamental class of `CPⁿ` at every point.
* `TauCeti.IsFundamentalClass.livesOverFundamentalClass_hopfSphere2`: a fundamental class of `S³`
  lives over the fundamental class of `S²` at every point, for the Hopf map `S³ → S²`.
* `TauCeti.exists_isFundamentalClass_and_livesOverFundamentalClass_hopfSphere2`:
  such a fundamental class exists.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4 (Definition 2.3, Example 2.4 and
  Remark 2.10).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §4.2,
  Example 4.45 (the Hopf fibration).
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Metric Module

namespace TauCeti

namespace ComplexProjectiveSpace

variable {n : ℕ}

/-- **The shriek map of a point for the Hopf fibration.** For a point `b` of the affine open
`{X_k ≠ 0}` of `CPⁿ`, the map `j_! : H₂ₙ₊₁(S²ⁿ⁺¹) → H₁(F)` to the homology of the fibre `F` of the
Hopf fibration over `b`: the localization `H₂ₙ₊₁(S²ⁿ⁺¹) → H₂ₙ₊₁(S²ⁿ⁺¹, S²ⁿ⁺¹ ∖ F)` at the fibre,
followed by the identification of its target with `H₁(F)` in the affine chart at `k`. -/
def hopfShriek (R : Type) [Ring R] (k : Fin (n + 1)) {b : ComplexProjectiveSpace n}
    (hb : b ∈ affineOpen k) :
    ((_root_.TopCat.toSSet.obj
      (_root_.TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1))).homology
        (ModuleCat.of R R) (2 * n + 1) : ModuleCat.{0} R) →ₗ[R]
      (((singularHomologyFunctor (ModuleCat.{0} R) 1).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (hopfHom n ⁻¹' {b})) : ModuleCat.{0} R) :=
  (TopCat.singularHomologyComplFiberIso (ModuleCat.of R R) (affineChart k)
    (by rwa [affineChart_source]) (ε := 1) (by simp) one_pos (mk_mem_serreFibrations n) 1
    (2 * n + 1) (by rw [finrank_real_of_complex, Module.finrank_fin_fun]; ring)).hom.hom ∘ₗ
    (fiberLocalization (ModuleCat.of R R) (hopfHom n) b (2 * n + 1)).hom

/-- The shriek map `TauCeti.ComplexProjectiveSpace.hopfShriek` is the localization at the fibre,
followed by `TauCeti.TopCat.singularHomologyComplFiberIso` for the affine chart at `k`. -/
theorem hopfShriek_apply (R : Type) [Ring R] (k : Fin (n + 1)) {b : ComplexProjectiveSpace n}
    (hb : b ∈ affineOpen k)
    (μ : ((_root_.TopCat.toSSet.obj
      (_root_.TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1))).homology
        (ModuleCat.of R R) (2 * n + 1) : ModuleCat.{0} R)) :
    hopfShriek R k hb μ =
      (TopCat.singularHomologyComplFiberIso (ModuleCat.of R R) (affineChart k)
        (by rwa [affineChart_source]) (ε := 1) (by simp) one_pos (mk_mem_serreFibrations n) 1
        (2 * n + 1) (by rw [finrank_real_of_complex, Module.finrank_fin_fun]; ring)).hom.hom
        ((fiberLocalization (ModuleCat.of R R) (hopfHom n) b (2 * n + 1)).hom μ) :=
  (rfl)

/-- The **class of the fibre** of the Hopf fibration over `[v]`: the integral class of the loop
`t ↦ e^{2πit} v`, the image of the circuit class of `ℝ / ℤ` under
`TauCeti.ComplexProjectiveSpace.hopfFiberCircleHomeomorph`. -/
def hopfFiberClass (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
      (_root_.TopCat.of (hopfHom n ⁻¹' {mk n v})) : ModuleCat.{0} ℤ) :=
  (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom (hopfFiberCircleHomeomorph v : C(AddCircle (1 : ℝ), _)))).hom
      (AddCircle.fundamentalClass 1)

theorem hopfFiberClass_def (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    hopfFiberClass v =
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (hopfFiberCircleHomeomorph v : C(AddCircle (1 : ℝ), _)))).hom
          (AddCircle.fundamentalClass 1) :=
  (rfl)

/-- The class of the fibre of the Hopf fibration is a fundamental class of the fibre. -/
theorem isFundamentalClass_hopfFiberClass (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    IsFundamentalClass (M := hopfHom n ⁻¹' {mk n v}) (hopfFiberClass v) :=
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  (AddCircle.isFundamentalClass_fundamentalClass 1).map_homeomorph _

end ComplexProjectiveSpace

open ComplexProjectiveSpace

namespace IsFundamentalClass

variable {n : ℕ} {R : Type} [Ring R]

/-- **The shriek map of a point for the Hopf fibration sends fundamental classes to fundamental
classes**: if `μ` is a fundamental class of `S²ⁿ⁺¹`, then `j_! μ` is a fundamental class of the
fibre circle over `b`. This is `j_![S²ⁿ⁺¹] = [S¹]` (Barraud–Damian–Humilière–Oancea, Remark 2.10),
up to the orientation conventions which `TauCeti.IsFundamentalClass` leaves free. -/
theorem hopfShriek (k : Fin (n + 1)) {b : ComplexProjectiveSpace n} (hb : b ∈ affineOpen k)
    {μ : ((_root_.TopCat.toSSet.obj
      (_root_.TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1))).homology
        (ModuleCat.of R R) (2 * n + 1) : ModuleCat.{0} R)} (hμ : IsFundamentalClass μ) :
    IsFundamentalClass (M := hopfHom n ⁻¹' {b}) (hopfShriek R k hb μ) := by
  rw [hopfShriek_apply]
  exact hμ.singularHomologyComplFiberIso_hom_fiberLocalization (n := 1) (affineChart k)
    (by rwa [affineChart_source]) (by simp) one_pos (mk_mem_serreFibrations n)
    (hopfTrivialization k) (by simpa using (affineChart k).chartBall_subset_source b 1)
    (by rw [finrank_real_of_complex, Module.finrank_fin_fun]; ring)

/-- **The shriek of the fundamental class of `S²ⁿ⁺¹` is `±[S¹]`.** With integral coefficients, the
shriek map of the point `[v]` for the Hopf fibration sends a fundamental class of `S²ⁿ⁺¹` to the
class of the fibre circle `t ↦ e^{2πit} v` or to its negative. -/
theorem hopfShriek_eq_or_eq_neg_hopfFiberClass
    {v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1} (k : Fin (n + 1))
    (hb : mk n v ∈ affineOpen k)
    {μ : ((_root_.TopCat.toSSet.obj
      (_root_.TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1))).homology
        (ModuleCat.of ℤ ℤ) (2 * n + 1) : ModuleCat.{0} ℤ)} (hμ : IsFundamentalClass μ) :
    ComplexProjectiveSpace.hopfShriek ℤ k hb μ = hopfFiberClass v ∨
      ComplexProjectiveSpace.hopfShriek ℤ k hb μ = -hopfFiberClass v := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let e := hopfFiberCircleHomeomorph v
  let H := (singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)
  set x := ComplexProjectiveSpace.hopfShriek ℤ k hb μ
  -- Pulled back to `ℝ / ℤ`, the shriek of `μ` is a fundamental class, hence a unit multiple `c` of
  -- the circuit class.
  have hα := (hμ.hopfShriek k hb).map_homeomorph e.symm
  obtain ⟨c, hc, -⟩ := (AddCircle.isFundamentalClass_fundamentalClass 1).existsUnique_eq_smul
    (finrank_self ℝ) ((H.map (TopCat.ofHom (e.symm : C(_, AddCircle (1 : ℝ))))).hom x)
  rw [hc, (AddCircle.isFundamentalClass_fundamentalClass 1).isFundamentalClass_smul_iff
    (finrank_self ℝ), Int.isUnit_iff] at hα
  -- Pushing forward along `e` recovers the shriek of `μ`.
  have he : x = (H.map (TopCat.ofHom (e : C(AddCircle (1 : ℝ), _)))).hom
      ((H.map (TopCat.ofHom (e.symm : C(_, AddCircle (1 : ℝ))))).hom x) :=
    (congrArg (fun φ ↦ φ.hom x)
      (H.mapIso (TopCat.isoOfHomeo (X := _root_.TopCat.of (AddCircle (1 : ℝ))) e)).inv_hom_id).symm
  rw [he, hc]
  -- `c • -` is the module structure of the homology, which is the `ℤ`-action of its additive group
  rcases hα with rfl | rfl
  · exact Or.inl (congrArg _ ((int_smul_eq_zsmul _ _ _).trans (one_zsmul _)))
  · exact Or.inr ((congrArg _ ((int_smul_eq_zsmul _ _ _).trans (neg_one_zsmul _))).trans
      (map_neg _ _))

/-- **The fundamental class of `S²ⁿ⁺¹` lives over the fundamental class of `CPⁿ`** for the Hopf
fibration, at every point of `CPⁿ` and with coefficients in every nontrivial ring: its shriek is
a fundamental class of the fibre circle, which is nonzero. -/
theorem livesOverFundamentalClass_hopfHom [Nontrivial R]
    {μ : ((_root_.TopCat.toSSet.obj
      (_root_.TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1))).homology
        (ModuleCat.of R R) (2 * n + 1) : ModuleCat.{0} R)} (hμ : IsFundamentalClass μ)
    (b : ComplexProjectiveSpace n) :
    LivesOverFundamentalClass (ModuleCat.of R R) (hopfHom n) b μ := by
  obtain ⟨v, rfl⟩ := mk_surjective n b
  obtain ⟨k, hk⟩ := exists_mem_affineOpen (mk n v)
  rw [livesOverFundamentalClass_iff]
  intro h0
  -- Otherwise the shriek of `μ` would be zero, and zero is not a fundamental class of a circle.
  have h := (hμ.hopfShriek k hk).map_homeomorph (hopfFiberCircleHomeomorph v).symm
  rw [hopfShriek_apply, h0, map_zero, map_zero] at h
  exact not_isFundamentalClass_zero (M := AddCircle (1 : ℝ)) (finrank_self ℝ) _ h

/-- **`[S³]` lives over `[S²]` for the Hopf map `S³ → S²`**, at every point of `S²` and with
coefficients in every nontrivial ring. -/
theorem livesOverFundamentalClass_hopfSphere2 [Nontrivial R]
    {μ : ((_root_.TopCat.toSSet.obj
      (_root_.TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))).homology
        (ModuleCat.of R R) 3 : ModuleCat.{0} R)} (hμ : IsFundamentalClass μ) (x : Sphere2) :
    LivesOverFundamentalClass (ModuleCat.of R R) hopfSphere2 x μ := by
  -- The fibre of `S³ → S²` over `x` is the fibre of `S³ → CP¹` over the corresponding point.
  refine (livesOverFundamentalClass_congr _ (Set.ext fun v ↦ ?_) μ).1
    (hμ.livesOverFundamentalClass_hopfHom (n := 1) (homeomorphSphere2.symm x))
  simp only [Set.mem_preimage, Set.mem_singleton_iff, ConcreteCategory.hom_ofHom,
    ContinuousMap.coe_mk, ← homeomorphSphere2_symm_hopfSphere2]
  exact homeomorphSphere2.symm.injective.eq_iff

end IsFundamentalClass

/-- **`S³` has a fundamental class living over `[S²]`** for the Hopf map `S³ → S²`, with
coefficients in every nontrivial ring: the sphere `S³` has a fundamental class
(`TauCeti.exists_isFundamentalClass_sphere`), and every fundamental class lives over the
fundamental class of `S²` at every point. -/
theorem exists_isFundamentalClass_and_livesOverFundamentalClass_hopfSphere2 (R : Type) [Ring R]
    [Nontrivial R] :
    ∃ μ : ((_root_.TopCat.toSSet.obj
      (_root_.TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1))).homology
        (ModuleCat.of R R) 3 : ModuleCat.{0} R),
      IsFundamentalClass μ ∧
        ∀ x : Sphere2, LivesOverFundamentalClass (ModuleCat.of R R) hopfSphere2 x μ :=
  have ⟨μ, hμ⟩ := exists_isFundamentalClass_sphere (E := EuclideanSpace ℂ (Fin 2)) (d := 2)
    (by rw [finrank_real_of_complex, finrank_euclideanSpace_fin]) R
  ⟨μ, hμ, hμ.livesOverFundamentalClass_hopfSphere2⟩

end TauCeti
