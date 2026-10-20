/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.Geometry.Manifold.Distribution.VectorBundle
public import TauCeti.Geometry.Manifold.Foliation.Taut
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Topology.VectorBundle.EulerClass

/-!
# The Euler class of a foliation and Thurston's Euler class one conjecture

The tangent field of a foliation `F` of rank `k` of a real manifold `M` is a real vector bundle of
rank `k` (`TauCeti.IsContMDiffDistribution.vectorBundle`). An orientation of it is a Thom class
`u ∈ Hᵏ(TF, TF₀)` (`TauCeti.Foliation.IsThomClass`), and its Euler class is the class
`e(u) ∈ Hᵏ(M)` of `TauCeti.eulerClass` (`TauCeti.Foliation.eulerClass`). A class `e ∈ Hᵏ(M)` is
*an Euler class of `F`* (`TauCeti.Foliation.IsEulerClass`) when it is `e(u)` for some orientation
`u` of the tangent field. Reversing the orientation negates the Euler class, and a tangent field
with a nowhere-vanishing continuous section has Euler class zero.

For a codimension-one foliation of a closed `3`-manifold the tangent field is a plane field, with
an Euler class in `H²(M; ℤ)`, and evaluating it on embedded surfaces bounds the topology of the
leaves. A class `e ∈ H²(X; ℤ)` satisfies the *Euler class inequality*
(`TauCeti.EulerClassBounded`) when `|⟨e, f_*[S]⟩| ≤ -χ(S)` for every closed connected oriented
surface `S` with `χ(S) ≤ 0` and every embedding `f : S → X`; here `⟨e, f_*[S]⟩` is the evaluation
`TauCeti.HomologicalOrientation.evalFundamentalClass` of `e` on the image of the fundamental
class. The inequality is *sharp* for `e` (`TauCeti.EulerClassNormOne`) when moreover equality
holds on some such surface with `χ(S) < 0`. On a closed hyperbolic `3`-manifold these two
conditions say that `e` has dual Thurston norm at most one, respectively exactly one: the Thurston
norm of a class is the least `-χ` of an embedded surface without sphere components representing
it, and by Gabai it is also the least `-χ` of a singular surface representing it, so merely
topological embeddings may be allowed. That equivalence is not formalized here; the two
predicates are the surface conditions themselves.

Thurston proved that the Euler class of a taut foliation of a closed hyperbolic `3`-manifold
satisfies the Euler class inequality (`TauCeti.ThurstonEulerClassInequality`), and conjectured
conversely that every even integral class for which the inequality is sharp is the Euler class of
a taut foliation (`TauCeti.EulerClassOneConjecture`). Evenness is necessary: the Euler class of an
oriented plane field `ξ` on a closed orientable `3`-manifold reduces mod `2` to
`w₂(ξ) = w₂(M) = 0`, so it is divisible by `2`. Yazdi found even counterexamples
(`TauCeti.YazdiEulerClassOneTheorem`), refuting the conjecture
(`TauCeti.YazdiEulerClassOneTheorem.not_eulerClassOneConjecture`). These statements are
recorded, not proved; foliations in them are smooth, so the counterexample statement is the
weakest form of Yazdi's theorem.

## Main definitions

* `TauCeti.Foliation.thomPair`: the Thom pair `(TF, TF₀)` of the tangent field of a foliation.
* `TauCeti.Foliation.IsThomClass`: an orientation of the tangent field, as a Thom class.
* `TauCeti.Foliation.eulerClass`: the Euler class `Hᵏ(TF, TF₀) ⟶ Hᵏ(M)`.
* `TauCeti.Foliation.IsEulerClass`: a class is the Euler class of some orientation of the
  tangent field.
* `TauCeti.EulerClassBounded`, `TauCeti.EulerClassNormOne`: the Euler class inequality on
  embedded surfaces, and its sharpness.
* `TauCeti.ThurstonEulerClassInequality`, `TauCeti.EulerClassOneConjecture`,
  `TauCeti.YazdiEulerClassOneTheorem`: Thurston's inequality, his Euler class one conjecture, and
  Yazdi's counterexample.

## Main results

* `TauCeti.Foliation.IsEulerClass.neg`: the negative of an Euler class is an Euler class.
* `TauCeti.Foliation.eulerClass_eq_zero_of_forall_ne_zero`: a nowhere-vanishing continuous
  tangent vector field kills the Euler class.
* `TauCeti.not_eulerClassNormOne_zero`: the inequality is never sharp for the zero class.
* `TauCeti.YazdiEulerClassOneTheorem.not_eulerClassOneConjecture`: Yazdi's theorem refutes the
  Euler class one conjecture.

## References

* W. P. Thurston, *A norm for the homology of 3-manifolds*, Mem. Amer. Math. Soc. 59 (1986),
  no. 339 (the Thurston norm, the Euler class inequality and the Euler class one conjecture).
* D. Gabai, *Foliations and the topology of 3-manifolds*, J. Differential Geom. 18 (1983),
  445–503, Section 6 (the Thurston norm is computed by singular surfaces).
* M. Yazdi, *On Thurston's Euler class-one conjecture*, Acta Math. 225 (2020), 313–368.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module Topology
open scoped Manifold ContDiff

universe w v u

namespace TauCeti

namespace Foliation

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ} [IsManifold I (n + 1) M]
  (F : Foliation I n M k)

/-- The Thom pair `(TF, TF₀)` of the tangent field `TF` of a foliation: the total space of the
tangent field, as a subspace of the tangent bundle, relative to its nonzero vectors. -/
abbrev thomPair : TopPair.{w} :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  TauCeti.thomPair (Fin k → ℝ) fun x ↦ F.distribution x

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {K : Type*} [Ring K] [Linear K C] {N : C}

/-- An orientation of the tangent field of a foliation of rank `k`, recorded as a Thom class
`u ∈ Hᵏ(TF, TF₀)` (`TauCeti.IsThomClass`): a relative class restricting to a generator of the
cohomology of every fibre pair. -/
def IsThomClass (u : F.thomPair.singularCohomology R K N (finrank ℝ (Fin k → ℝ))) : Prop :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI := F.isContMDiffDistribution.fiberBundle
  TauCeti.IsThomClass (Fin k → ℝ) (fun x ↦ F.distribution x) u

variable (R K N) in
/-- The Euler class `Hᵏ(TF, TF₀) ⟶ Hᵏ(M)` of the tangent field of a foliation of rank `k`:
`TauCeti.eulerClass`, restriction to the total space followed by pullback along the zero
section, read in degree `k`. -/
def eulerClass :
    F.thomPair.singularCohomology R K N (finrank ℝ (Fin k → ℝ)) ⟶
      (TopCat.of M).singularCohomology R K N k :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI := F.isContMDiffDistribution.fiberBundle
  haveI := F.isContMDiffDistribution.vectorBundle
  TauCeti.eulerClass R K N (Fin k → ℝ) (fun x ↦ F.distribution x) _ ≫
    eqToHom (by rw [finrank_fin_fun])

/-- A class `e ∈ Hᵏ(M)` is an Euler class of the foliation `F` of rank `k` when it is the Euler
class of some orientation of the tangent field of `F`. -/
def IsEulerClass (e : (TopCat.of M).singularCohomology R K N k) : Prop :=
  ∃ u : F.thomPair.singularCohomology R K N (finrank ℝ (Fin k → ℝ)),
    F.IsThomClass u ∧ F.eulerClass R K N u = e

/-- The defining property of an orientation of the tangent field. -/
theorem isThomClass_iff {u : F.thomPair.singularCohomology R K N (finrank ℝ (Fin k → ℝ))} :
    F.IsThomClass u ↔
      letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
      letI := F.isContMDiffDistribution.fiberBundle
      TauCeti.IsThomClass (Fin k → ℝ) (fun x ↦ F.distribution x) u :=
  Iff.rfl

/-- The Euler class of a foliation is that of its tangent field, read in degree `k`. -/
theorem eulerClass_def [IsManifold I 1 M] :
    F.eulerClass R K N =
      letI := F.isContMDiffDistribution.fiberBundle
      haveI := F.isContMDiffDistribution.vectorBundle
      TauCeti.eulerClass R K N (Fin k → ℝ) (fun x ↦ F.distribution x) _ ≫
        eqToHom (by rw [finrank_fin_fun]) :=
  (rfl)

/-- The defining property of an Euler class of a foliation. -/
theorem isEulerClass_iff {e : (TopCat.of M).singularCohomology R K N k} :
    F.IsEulerClass e ↔ ∃ u : F.thomPair.singularCohomology R K N (finrank ℝ (Fin k → ℝ)),
      F.IsThomClass u ∧ F.eulerClass R K N u = e :=
  Iff.rfl

variable {F}

/-- The Euler class of an orientation of the tangent field is an Euler class of the foliation. -/
theorem isEulerClass_eulerClass {u : F.thomPair.singularCohomology R K N (finrank ℝ (Fin k → ℝ))}
    (hu : F.IsThomClass u) : F.IsEulerClass (F.eulerClass R K N u) :=
  ⟨u, hu, rfl⟩

/-- The negative of a Thom class of the tangent field is a Thom class: the reversed
orientation. -/
theorem IsThomClass.neg {u : F.thomPair.singularCohomology R K N (finrank ℝ (Fin k → ℝ))}
    (hu : F.IsThomClass u) : F.IsThomClass (-u) :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI := F.isContMDiffDistribution.fiberBundle
  TauCeti.IsThomClass.neg hu

/-- Reversing the orientation of the tangent field negates its Euler class. -/
theorem IsEulerClass.neg {e : (TopCat.of M).singularCohomology R K N k} (he : F.IsEulerClass e) :
    F.IsEulerClass (-e) := by
  obtain ⟨u, hu, rfl⟩ := he
  exact ⟨-u, hu.neg, map_neg _ u⟩

variable (F R K N) in
/-- **A nowhere-vanishing tangent vector field kills the Euler class.** If the tangent field of
`F` has a section `s` that is continuous as a vector field on `M` and vanishes nowhere, then the
Euler class map of `F` is zero, so `0` is the only possible Euler class of `F`. The instance
`IsManifold I 1 M`, implied by the `C^(n + 1)` structure, gives the tangent bundle its
topology. -/
theorem eulerClass_eq_zero_of_forall_ne_zero [IsManifold I 1 M] {s : ∀ x, F.distribution x}
    (hs : Continuous fun x ↦ (⟨x, s x⟩ : TangentBundle I M)) (hs₀ : ∀ x, s x ≠ 0) :
    F.eulerClass R K N = 0 := by
  let := F.isContMDiffDistribution.fiberBundle
  have := F.isContMDiffDistribution.vectorBundle
  rw [eulerClass_def, TauCeti.eulerClass_eq_zero_of_forall_ne_zero (Fin k → ℝ) _
    (continuous_induced_rng.2 hs) hs₀, zero_comp]

/-- If the tangent field of `F` has a continuous nowhere-vanishing section, then every Euler
class of `F` is zero. -/
theorem IsEulerClass.eq_zero_of_forall_ne_zero [IsManifold I 1 M]
    {e : (TopCat.of M).singularCohomology R K N k} (he : F.IsEulerClass e)
    {s : ∀ x, F.distribution x} (hs : Continuous fun x ↦ (⟨x, s x⟩ : TangentBundle I M))
    (hs₀ : ∀ x, s x ≠ 0) : e = 0 := by
  obtain ⟨u, -, rfl⟩ := he
  rw [eulerClass_eq_zero_of_forall_ne_zero F R K N hs hs₀]
  simp

end Foliation

/-! ### The Euler class inequality -/

section Inequality

variable {X : Type} [TopologicalSpace X]

/-- The **Euler class inequality** for an integral class `e ∈ H²(X; ℤ)`: for every closed
connected oriented surface `S` of Euler characteristic `χ(S) ≤ 0` and every embedding
`f : S → X`, the evaluation of `e` on `f_*[S]` satisfies `|⟨e, f_*[S]⟩| ≤ -χ(S)`. Closed
surfaces have finite CW type, which makes `χ(S)` defined. On a closed hyperbolic `3`-manifold
this says that `e` has dual Thurston norm at most one. -/
def EulerClassBounded
    (e : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ ℤ) 2) :
    Prop :=
  ∀ (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [CompactSpace S] [ConnectedSpace S] [FiniteCWType S]
    (o : HomologicalOrientation S (EuclideanSpace ℝ (Fin 2)) 2) (f : C(S, X)),
    IsEmbedding f → eulerChar S ≤ 0 →
      |o.evalFundamentalClass finrank_euclideanSpace_fin (ModuleCat.of ℤ ℤ) f e| ≤ -eulerChar S

/-- The Euler class inequality is **sharp** for an integral class `e ∈ H²(X; ℤ)` when `e`
satisfies it and some closed connected oriented surface `S` with `χ(S) < 0` embeds in `X` by an
`f` with `|⟨e, f_*[S]⟩| = -χ(S)`. On a closed hyperbolic `3`-manifold this says that `e` has
dual Thurston norm exactly one. -/
def EulerClassNormOne
    (e : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ ℤ) 2) :
    Prop :=
  EulerClassBounded e ∧
    ∃ (S : Type) (_ : TopologicalSpace S) (_ : T2Space S)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S) (_ : CompactSpace S) (_ : ConnectedSpace S)
      (_ : FiniteCWType S) (o : HomologicalOrientation S (EuclideanSpace ℝ (Fin 2)) 2)
      (f : C(S, X)), IsEmbedding f ∧ eulerChar S < 0 ∧
        |o.evalFundamentalClass finrank_euclideanSpace_fin (ModuleCat.of ℤ ℤ) f e| =
          -eulerChar S

variable {e : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
  (ModuleCat.of ℤ ℤ) 2}

/-- A class satisfying the Euler class inequality obeys the bound `|⟨e, f_*[S]⟩| ≤ -χ(S)` on
every embedded closed connected oriented surface `S` with `χ(S) ≤ 0`. -/
theorem EulerClassBounded.abs_le (he : EulerClassBounded e) (S : Type) [TopologicalSpace S]
    [T2Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [CompactSpace S] [ConnectedSpace S]
    [FiniteCWType S] (o : HomologicalOrientation S (EuclideanSpace ℝ (Fin 2)) 2) {f : C(S, X)}
    (hf : IsEmbedding f) (hS : eulerChar S ≤ 0) :
    |o.evalFundamentalClass finrank_euclideanSpace_fin (ModuleCat.of ℤ ℤ) f e| ≤ -eulerChar S :=
  he S o f hf hS

/-- The zero class satisfies the Euler class inequality. -/
theorem eulerClassBounded_zero :
    EulerClassBounded (0 : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 2) := by
  intro S _ _ _ _ _ _ o f _ hS
  simpa using hS

/-- A class satisfies the Euler class inequality exactly when its negative does. -/
@[simp]
theorem eulerClassBounded_neg_iff : EulerClassBounded (-e) ↔ EulerClassBounded e := by
  simp only [EulerClassBounded, map_neg, abs_neg]

alias ⟨_, EulerClassBounded.neg⟩ := eulerClassBounded_neg_iff

/-- A class satisfying the Euler class inequality vanishes on every embedded closed connected
oriented surface of Euler characteristic zero, such as an embedded torus. -/
theorem EulerClassBounded.evalFundamentalClass_eq_zero (he : EulerClassBounded e) (S : Type)
    [TopologicalSpace S] [T2Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [CompactSpace S] [ConnectedSpace S] [FiniteCWType S]
    (o : HomologicalOrientation S (EuclideanSpace ℝ (Fin 2)) 2) {f : C(S, X)}
    (hf : IsEmbedding f) (hS : eulerChar S = 0) :
    o.evalFundamentalClass finrank_euclideanSpace_fin (ModuleCat.of ℤ ℤ) f e = 0 :=
  abs_nonpos_iff.mp ((he.abs_le S o hf hS.le).trans (by rw [hS, neg_zero]))

/-- A class satisfying the Euler class inequality is sharp for it once some embedded closed
connected oriented surface `S` with `χ(S) < 0` has `|⟨e, f_*[S]⟩| = -χ(S)`. -/
theorem EulerClassBounded.eulerClassNormOne (he : EulerClassBounded e) (S : Type)
    [TopologicalSpace S] [T2Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [CompactSpace S] [ConnectedSpace S] [FiniteCWType S]
    (o : HomologicalOrientation S (EuclideanSpace ℝ (Fin 2)) 2) {f : C(S, X)}
    (hf : IsEmbedding f) (hS : eulerChar S < 0)
    (heq : |o.evalFundamentalClass finrank_euclideanSpace_fin (ModuleCat.of ℤ ℤ) f e| =
      -eulerChar S) :
    EulerClassNormOne e :=
  ⟨he, S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, o, f, hf, hS, heq⟩

/-- A class for which the Euler class inequality is sharp satisfies it. -/
theorem EulerClassNormOne.eulerClassBounded (he : EulerClassNormOne e) : EulerClassBounded e :=
  he.1

/-- A class for which the Euler class inequality is sharp has a sharpness witness: an embedded
closed connected oriented surface `S` with `χ(S) < 0` and `|⟨e, f_*[S]⟩| = -χ(S)`. -/
theorem EulerClassNormOne.exists_abs_eq (he : EulerClassNormOne e) :
    ∃ (S : Type) (_ : TopologicalSpace S) (_ : T2Space S)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S) (_ : CompactSpace S) (_ : ConnectedSpace S)
      (_ : FiniteCWType S) (o : HomologicalOrientation S (EuclideanSpace ℝ (Fin 2)) 2)
      (f : C(S, X)), IsEmbedding f ∧ eulerChar S < 0 ∧
        |o.evalFundamentalClass finrank_euclideanSpace_fin (ModuleCat.of ℤ ℤ) f e| =
          -eulerChar S :=
  he.2

/-- The Euler class inequality is sharp for a class exactly when it is sharp for its
negative. -/
@[simp]
theorem eulerClassNormOne_neg_iff : EulerClassNormOne (-e) ↔ EulerClassNormOne e := by
  simp only [EulerClassNormOne, eulerClassBounded_neg_iff, map_neg, abs_neg]

alias ⟨_, EulerClassNormOne.neg⟩ := eulerClassNormOne_neg_iff

/-- The Euler class inequality is never sharp for the zero class. -/
theorem not_eulerClassNormOne_zero :
    ¬ EulerClassNormOne (0 : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℤ) 2) := by
  rintro ⟨-, S, _, _, _, _, _, _, o, f, -, hS, h⟩
  simp only [map_zero, abs_zero] at h
  omega

end Inequality

/-! ### Thurston's Euler class one conjecture -/

/-- **Thurston's Euler class inequality**: on a closed orientable hyperbolic `3`-manifold `M`,
that is a compact connected orientable smooth `3`-manifold without boundary admitting a complete
Riemannian metric of constant curvature `-1`, every Euler class of a smooth taut codimension-one
foliation satisfies the Euler class inequality. -/
def ThurstonEulerClassInequality : Prop :=
  ∀ (M : Type) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M] [Orientable (𝓡 3) M],
    IsHyperbolic (I := 𝓡 3) (M := M) →
      haveI : IsManifold (𝓡 3) (∞ + 1) M := .of_le (n := ∞) (by simp)
      ∀ (F : Foliation (𝓡 3) ∞ M 2), F.Taut →
        ∀ e : (TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          (ModuleCat.of ℤ ℤ) 2, F.IsEulerClass e → EulerClassBounded e

/-- **Thurston's Euler class one conjecture**: on a closed orientable hyperbolic `3`-manifold `M`,
every even integral class `e ∈ H²(M; ℤ)` for which the Euler class inequality is sharp is an
Euler class of a smooth taut codimension-one foliation of `M`. Evenness is necessary, since the
Euler class of an oriented plane field on `M` reduces mod `2` to `w₂(M) = 0`.

The conjecture is false, by Yazdi
(`TauCeti.YazdiEulerClassOneTheorem.not_eulerClassOneConjecture`). -/
def EulerClassOneConjecture : Prop :=
  ∀ (M : Type) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M] [Orientable (𝓡 3) M],
    IsHyperbolic (I := 𝓡 3) (M := M) →
      haveI : IsManifold (𝓡 3) (∞ + 1) M := .of_le (n := ∞) (by simp)
      ∀ e : (TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
        (ModuleCat.of ℤ ℤ) 2, Even e → EulerClassNormOne e →
          ∃ F : Foliation (𝓡 3) ∞ M 2, F.Taut ∧ F.IsEulerClass e

section ClosedHyperbolic

variable {M : Type} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M] [Orientable (𝓡 3) M]

/-- Under Thurston's Euler class inequality, every Euler class of a smooth taut codimension-one
foliation of a closed orientable hyperbolic `3`-manifold satisfies the Euler class
inequality. -/
theorem ThurstonEulerClassInequality.eulerClassBounded (h : ThurstonEulerClassInequality)
    (hM : IsHyperbolic (I := 𝓡 3) (M := M)) :
    haveI : IsManifold (𝓡 3) (∞ + 1) M := .of_le (n := ∞) (by simp)
    ∀ (F : Foliation (𝓡 3) ∞ M 2), F.Taut →
      ∀ e : (TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
        (ModuleCat.of ℤ ℤ) 2, F.IsEulerClass e → EulerClassBounded e :=
  h M hM

/-- Under the Euler class one conjecture, every even integral class of a closed orientable
hyperbolic `3`-manifold for which the Euler class inequality is sharp is an Euler class of a
smooth taut codimension-one foliation. -/
theorem EulerClassOneConjecture.exists_taut_isEulerClass (h : EulerClassOneConjecture)
    (hM : IsHyperbolic (I := 𝓡 3) (M := M))
    {e : (TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ ℤ) 2}
    (he₂ : Even e) (he : EulerClassNormOne e) :
    haveI : IsManifold (𝓡 3) (∞ + 1) M := .of_le (n := ∞) (by simp)
    ∃ F : Foliation (𝓡 3) ∞ M 2, F.Taut ∧ F.IsEulerClass e :=
  h M hM e he₂ he

end ClosedHyperbolic

/-- **Yazdi's theorem**: some closed orientable hyperbolic `3`-manifold `M` carries an even
integral class `e ∈ H²(M; ℤ)` for which the Euler class inequality is sharp, but which is not an
Euler class of any smooth taut codimension-one foliation of `M`. -/
def YazdiEulerClassOneTheorem : Prop :=
  ∃ (M : Type) (_ : MetricSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M)
    (_ : IsManifold (𝓡 3) ∞ M) (_ : CompactSpace M) (_ : ConnectedSpace M)
    (_ : Orientable (𝓡 3) M), IsHyperbolic (I := 𝓡 3) (M := M) ∧
      haveI : IsManifold (𝓡 3) (∞ + 1) M := .of_le (n := ∞) (by simp)
      ∃ e : (TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
        (ModuleCat.of ℤ ℤ) 2, Even e ∧ EulerClassNormOne e ∧
          ∀ F : Foliation (𝓡 3) ∞ M 2, F.Taut → ¬ F.IsEulerClass e

/-- **Yazdi's theorem refutes the Euler class one conjecture.** -/
theorem YazdiEulerClassOneTheorem.not_eulerClassOneConjecture (h : YazdiEulerClassOneTheorem) :
    ¬ EulerClassOneConjecture := by
  intro hc
  obtain ⟨M, _, _, _, _, _, _, hM, e, he₂, he, hF⟩ := h
  obtain ⟨F, hF₁, hF₂⟩ := hc.exists_taut_isEulerClass hM he₂ he
  exact hF F hF₁ hF₂

end TauCeti
