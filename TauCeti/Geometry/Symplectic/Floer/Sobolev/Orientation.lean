/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Homotopy
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Fredholm
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Floer.Continuation
import TauCeti.Geometry.Symplectic.Floer.Continuation.AlmostComplex

/-!
# Orientation transport for the linearized Floer operator along paths of Floer data

Let `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` be the Sobolev realization
(`TauCeti.SymplecticForm.floerSobolevOperator`) of the linearized Floer operator along a map `u`
of the cylinder into a finite-dimensional complex inner product space `F` with `ω = Im ⟪·, ·⟫`,
asymptotic to nondegenerate one-periodic orbits `x₋` and `x₊` of fixed end Hamiltonians `H₋` and
`H₊`. For Floer data `(J, K_s, K_t)` with compatible almost complex structures, cylindrical near
the ends with these end Hamiltonians, `D_u` is Fredholm
(`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible`), so it has a
determinant line `det (ker D_u) ⊗ (det (coker D_u))^*`. Orienting the moduli spaces of Floer
trajectories starts from orientations of these lines, and they must be compared for different
choices of the data.

Along a path `μ ↦ (J_μ, K_{s,μ}, K_{t,μ})` of such data, jointly `C¹` in the parameter (with `C²`
Hamiltonians), the operators `D_u` depend continuously on `μ` in the operator norm
(`TauCeti.SymplecticForm.continuousOn_floerSobolevOperator_family`), so orientations of their
determinant lines are transported along the path (`TauCeti.detLineOrientationTransport`). This
file proves that the transport depends only on the endpoints of the path
(`TauCeti.SymplecticForm.detLineOrientationTransport_floerSobolevOperator_congr`): for two paths of
data with the same end Hamiltonians, defined on `[[a, b]]` and agreeing at `a` and at `b`, the
transports from `a` to `b` along the two paths agree, once the determinant lines of the equal
operators at `a` and at `b` are identified. The almost complex structures of the ends may move
along the paths. So an orientation of the determinant line of `D_u` for one choice of data
determines one for every other choice with the same end Hamiltonians, independently of the path
of data used to compare them. In particular, transport around a loop of data is trivial
(`TauCeti.SymplecticForm.detLineOrientationTransport_floerSobolevOperator_eq_map`), so the
determinant lines are orientable over every loop of Floer data with fixed end Hamiltonians.

The proof joins the two paths by a homotopy of data relative to the endpoints. Its Hamiltonians
run along the segment between those of the two paths, and its almost complex structures along the
continuation homotopy `TauCeti.Floer.continuationAlmostComplex`, whose Cayley coordinates
relative to the complex structure of `F` run along the segment between those of the two paths, so
that they stay compatible. The homotopy of data is cylindrical near the ends with the same end
Hamiltonians and is `C¹` in both parameters, so its operators are Fredholm and continuous on the
parameter rectangle, and orientation transport is invariant under it
(`TauCeti.detLineOrientationTransport_eq_of_homotopy_of_eq`).

## Main results

* `TauCeti.SymplecticForm.detLineOrientationTransport_floerSobolevOperator_congr`: orientation
  transport of the determinant lines of `D_u` along a path of Floer data with fixed end
  Hamiltonians depends only on the data at the endpoints.
* `TauCeti.SymplecticForm.detLineOrientationTransport_floerSobolevOperator_eq_map`: orientation
  transport around a loop of Floer data with fixed end Hamiltonians is trivial.

## References

* A. Floer and H. Hofer, *Coherent orientations for periodic orbit problems in symplectic
  geometry*, Math. Z. 212 (1993), 13–38, on orienting the determinant lines of the linearized
  Floer operators through the contractibility of the spaces of data with fixed asymptotics.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Section 2.5, on the
  Cayley transform and the convexity of the space of compatible structures.
-/

public section

open Filter Set Function
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev

section HamiltonianHomotopy

variable {V : Type*}

/-- The homotopy between two paths `K₁` and `K₂` of Hamiltonians on the cylinder: at
`((σ, μ), z)` it is the linear homotopy `K₁ (μ, z) + σ (K₂ (μ, z) - K₁ (μ, z))`. -/
private def homotopyHamiltonian (K₁ K₂ : ℝ × (ℝ × ℝ) → V → ℝ) (p : (ℝ × ℝ) × (ℝ × ℝ)) (y : V) :
    ℝ :=
  Floer.linearHomotopy id (fun _ q ↦ K₁ q.1 q.2) (fun _ q ↦ K₂ q.1 q.2) (p.1.1, 0)
    ((p.1.2, p.2), y)

/-- Where the two paths of Hamiltonians take a common value, so does the homotopy. -/
private theorem homotopyHamiltonian_of_eq {K₁ K₂ : ℝ × (ℝ × ℝ) → V → ℝ} (σ : ℝ) {μ : ℝ}
    {z : ℝ × ℝ} {e : V → ℝ} (h₁ : K₁ (μ, z) = e) (h₂ : K₂ (μ, z) = e) :
    homotopyHamiltonian K₁ K₂ ((σ, μ), z) = e :=
  funext fun y ↦ by simp [homotopyHamiltonian, Floer.linearHomotopy_def, h₁, h₂]

/-- The homotopy of Hamiltonians is `K₁` at `σ = 0`. -/
private theorem homotopyHamiltonian_zero (K₁ K₂ : ℝ × (ℝ × ℝ) → V → ℝ) (μ : ℝ) (z : ℝ × ℝ) :
    homotopyHamiltonian K₁ K₂ ((0, μ), z) = K₁ (μ, z) :=
  funext fun _ ↦ Floer.linearHomotopy_of_eq_zero (z := (0, 0)) rfl _

/-- The homotopy of Hamiltonians is `K₂` at `σ = 1`. -/
private theorem homotopyHamiltonian_one (K₁ K₂ : ℝ × (ℝ × ℝ) → V → ℝ) (μ : ℝ) (z : ℝ × ℝ) :
    homotopyHamiltonian K₁ K₂ ((1, μ), z) = K₂ (μ, z) :=
  funext fun _ ↦ Floer.linearHomotopy_of_eq_one (z := (1, 0)) rfl _

/-- The homotopy of Hamiltonians is `C²` when the two paths are. -/
private theorem contDiff_homotopyHamiltonian [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K₁ K₂ : ℝ × (ℝ × ℝ) → V → ℝ}
    (hK₁ : ContDiff ℝ 2 (uncurry K₁)) (hK₂ : ContDiff ℝ 2 (uncurry K₂)) :
    ContDiff ℝ 2 (uncurry (homotopyHamiltonian K₁ K₂)) := by
  have h := Floer.contDiff_uncurry_linearHomotopy (n := 2) (β := id)
    (H₀ := fun (_ : ℝ) (q : (ℝ × (ℝ × ℝ)) × V) ↦ K₁ q.1 q.2)
    (H₁ := fun (_ : ℝ) (q : (ℝ × (ℝ × ℝ)) × V) ↦ K₂ q.1 q.2) contDiff_id
    (hK₁.comp contDiff_snd) (hK₂.comp contDiff_snd)
  exact h.comp ((contDiff_fst.fst.fst.prodMk contDiff_const).prodMk
    ((contDiff_fst.fst.snd.prodMk contDiff_fst.snd).prodMk contDiff_snd))

end HamiltonianHomotopy

section Homotopy

/-! ### A homotopy between two paths of Floer data -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J₁ J₂ : ℝ × (ℝ × ℝ) → V → AlmostComplexStructure V} {hJ₁ : ∀ p y, ω.Tames (J₁ p y)}
  {hJ₂ : ∀ p y, ω.Tames (J₂ p y)}

/-- The homotopy between two paths `J₁` and `J₂` of almost complex structures on the cylinder: at
`((σ, μ), z)` and `y` it is the continuation homotopy, relative to `J₀`, from `J₁ (μ, z) y` to
`J₂ (μ, z) y` at the homotopy coordinate `s = σ`. -/
private noncomputable def homotopyAlmostComplex (h₀ : ω.Compatible J₀)
    (hJ₁ : ∀ p y, ω.Tames (J₁ p y)) (hJ₂ : ∀ p y, ω.Tames (J₂ p y)) (p : (ℝ × ℝ) × (ℝ × ℝ))
    (y : V) : AlmostComplexStructure V :=
  Floer.continuationAlmostComplex h₀ (fun _ q ↦ J₁ q.1 q.2) (fun _ q ↦ J₂ q.1 q.2)
    (fun _ q ↦ hJ₁ q.1 q.2) (fun _ q ↦ hJ₂ q.1 q.2) (p.1.1, 0) ((p.1.2, p.2), y)

/-- The homotopy of almost complex structures is `J₁` at `σ = 0`. -/
private theorem homotopyAlmostComplex_zero (h₀ : ω.Compatible J₀) (μ : ℝ) (z : ℝ × ℝ) :
    homotopyAlmostComplex h₀ hJ₁ hJ₂ ((0, μ), z) = J₁ (μ, z) :=
  funext fun _ ↦ Floer.continuationAlmostComplex_of_nonpos h₀ (z := (0, 0)) le_rfl _

/-- The homotopy of almost complex structures is `J₂` at `σ = 1`. -/
private theorem homotopyAlmostComplex_one (h₀ : ω.Compatible J₀) (μ : ℝ) (z : ℝ × ℝ) :
    homotopyAlmostComplex h₀ hJ₁ hJ₂ ((1, μ), z) = J₂ (μ, z) :=
  funext fun _ ↦ Floer.continuationAlmostComplex_of_one_le h₀ (z := (1, 0)) le_rfl _

/-- Where the two paths of almost complex structures agree, the homotopy is their common value. -/
private theorem homotopyAlmostComplex_of_eq (h₀ : ω.Compatible J₀) (σ : ℝ) {μ : ℝ} {z : ℝ × ℝ}
    (h : J₁ (μ, z) = J₂ (μ, z)) : homotopyAlmostComplex h₀ hJ₁ hJ₂ ((σ, μ), z) = J₁ (μ, z) :=
  funext fun y ↦ Floer.continuationAlmostComplex_of_eq h₀ (congrFun h y)

/-- At each point of the parameter square, the homotopy at `z` depends only on `J₁ (μ, z)` and
`J₂ (μ, z)`. -/
private theorem homotopyAlmostComplex_congr (h₀ : ω.Compatible J₀) (σ μ : ℝ) {z z' : ℝ × ℝ}
    (h₁ : J₁ (μ, z) = J₁ (μ, z')) (h₂ : J₂ (μ, z) = J₂ (μ, z')) :
    homotopyAlmostComplex h₀ hJ₁ hJ₂ ((σ, μ), z) = homotopyAlmostComplex h₀ hJ₁ hJ₂ ((σ, μ), z') :=
  funext fun y ↦ h₀.eq_of_cayley_eq (Floer.tames_continuationAlmostComplex h₀ _ _)
    (Floer.tames_continuationAlmostComplex h₀ _ _) (by
      simp only [homotopyAlmostComplex, Floer.cayley_continuationAlmostComplex, h₁, h₂])

/-- The homotopy of almost complex structures is `ω`-compatible where both paths are. -/
private theorem compatible_homotopyAlmostComplex (h₀ : ω.Compatible J₀)
    {p : (ℝ × ℝ) × (ℝ × ℝ)} {y : V} (h₁ : ω.Compatible (J₁ (p.1.2, p.2) y))
    (h₂ : ω.Compatible (J₂ (p.1.2, p.2) y)) :
    ω.Compatible (homotopyAlmostComplex h₀ hJ₁ hJ₂ p y) :=
  Floer.compatible_continuationAlmostComplex h₀ h₁ h₂

/-- The homotopy of almost complex structures is `C¹` jointly in the two parameters, the point
of the cylinder and the target point, when the two paths are. -/
private theorem contDiff_homotopyAlmostComplex (h₀ : ω.Compatible J₀)
    (hJ₁s : ContDiff ℝ 1 fun q : (ℝ × (ℝ × ℝ)) × V ↦
      (J₁ q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJ₂s : ContDiff ℝ 1 fun q : (ℝ × (ℝ × ℝ)) × V ↦
      (J₂ q.1 q.2).toLinearMap.toContinuousLinearMap) :
    ContDiff ℝ 1 fun q : ((ℝ × ℝ) × (ℝ × ℝ)) × V ↦
      (homotopyAlmostComplex h₀ hJ₁ hJ₂ q.1 q.2).toLinearMap.toContinuousLinearMap := by
  have h := Floer.contDiff_continuationAlmostComplex (F := (ℝ × (ℝ × ℝ)) × V) (n := 1) h₀
    (J₁ := fun _ q ↦ J₁ q.1 q.2) (J₂ := fun _ q ↦ J₂ q.1 q.2) (hJ₁ := fun _ q ↦ hJ₁ q.1 q.2)
    (hJ₂ := fun _ q ↦ hJ₂ q.1 q.2) (hJ₁s.comp contDiff_snd) (hJ₂s.comp contDiff_snd)
  exact h.comp ((contDiff_fst.fst.fst.prodMk contDiff_const).prodMk
    ((contDiff_fst.fst.snd.prodMk contDiff_fst.snd).prodMk contDiff_snd))

/-- The homotopy between two paths of data cylindrical near the ends with the same end
Hamiltonians, with radii `R₁` and `R₂`, is cylindrical near the ends with the radius
`max R₁ R₂` and the same end Hamiltonians. -/
private theorem isCylindricalNearEnds_homotopy (h₀ : ω.Compatible J₀)
    {Ks₁ Kt₁ Ks₂ Kt₂ : ℝ × (ℝ × ℝ) → V → ℝ} {Jm₁ Jp₁ Jm₂ Jp₂ : ℝ → V → AlmostComplexStructure V}
    {Hm Hp : ℝ → V → ℝ} {R₁ R₂ σ μ : ℝ} {u : ℝ × ℝ → V}
    (hcyl₁ : Floer.IsCylindricalNearEnds (fun w ↦ J₁ (μ, w)) (fun w ↦ Ks₁ (μ, w))
      (fun w ↦ Kt₁ (μ, w)) Jm₁ Jp₁ Hm Hp R₁ u)
    (hcyl₂ : Floer.IsCylindricalNearEnds (fun w ↦ J₂ (μ, w)) (fun w ↦ Ks₂ (μ, w))
      (fun w ↦ Kt₂ (μ, w)) Jm₂ Jp₂ Hm Hp R₂ u)
    (hJ : ContDiff ℝ 1 fun q : ((ℝ × ℝ) × (ℝ × ℝ)) × V ↦
      (homotopyAlmostComplex h₀ hJ₁ hJ₂ q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry (homotopyHamiltonian Ks₁ Ks₂)))
    (hKt : ContDiff ℝ 2 (uncurry (homotopyHamiltonian Kt₁ Kt₂))) :
    Floer.IsCylindricalNearEnds (fun w ↦ homotopyAlmostComplex h₀ hJ₁ hJ₂ ((σ, μ), w))
      (fun w ↦ homotopyHamiltonian Ks₁ Ks₂ ((σ, μ), w))
      (fun w ↦ homotopyHamiltonian Kt₁ Kt₂ ((σ, μ), w))
      (fun t ↦ homotopyAlmostComplex h₀ hJ₁ hJ₂ ((σ, μ), (-max R₁ R₂, t)))
      (fun t ↦ homotopyAlmostComplex h₀ hJ₁ hJ₂ ((σ, μ), (max R₁ R₂, t))) Hm Hp (max R₁ R₂) u := by
  have h₁ := hcyl₁.mono (le_max_left R₁ R₂)
  have h₂ := hcyl₂.mono (le_max_right R₁ R₂)
  exact
    { almostComplex_eq_of_le_neg := fun z hz ↦ homotopyAlmostComplex_congr h₀ σ μ
        ((h₁.almostComplex_eq_of_le_neg z hz).trans
          (h₁.almostComplex_eq_of_le_neg (_, z.2) le_rfl).symm)
        ((h₂.almostComplex_eq_of_le_neg z hz).trans
          (h₂.almostComplex_eq_of_le_neg (_, z.2) le_rfl).symm)
      almostComplex_eq_of_le := fun z hz ↦ homotopyAlmostComplex_congr h₀ σ μ
        ((h₁.almostComplex_eq_of_le z hz).trans (h₁.almostComplex_eq_of_le (_, z.2) le_rfl).symm)
        ((h₂.almostComplex_eq_of_le z hz).trans (h₂.almostComplex_eq_of_le (_, z.2) le_rfl).symm)
      hamiltonianS_eq_zero := fun z hz ↦ homotopyHamiltonian_of_eq σ
        (h₁.hamiltonianS_eq_zero z hz) (h₂.hamiltonianS_eq_zero z hz)
      hamiltonianT_eq_of_le_neg := fun z hz ↦ homotopyHamiltonian_of_eq σ
        (h₁.hamiltonianT_eq_of_le_neg z hz) (h₂.hamiltonianT_eq_of_le_neg z hz)
      hamiltonianT_eq_of_le := fun z hz ↦ homotopyHamiltonian_of_eq σ
        (h₁.hamiltonianT_eq_of_le z hz) (h₂.hamiltonianT_eq_of_le z hz)
      contDiffAt_almostComplex := fun _ ↦
        (contDiff_comp_prodMap_prodMk_right hJ (σ, μ)).contDiffAt
      contDiffAt_hamiltonianS := fun _ ↦
        (contDiff_comp_prodMap_prodMk_right hKs (σ, μ)).contDiffAt
      contDiffAt_hamiltonianT := fun _ ↦
        (contDiff_comp_prodMap_prodMk_right hKt (σ, μ)).contDiffAt }

end Homotopy

section Transport

/-! ### Path independence of orientation transport -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Orientation transport for the linearized Floer operator depends only on the endpoints of
the path of data.** Let `F` be a finite-dimensional complex inner product space whose symplectic
form `ω` is `Im ⟪·, ·⟫`, let `H±` be one-periodic, jointly `C³` time-dependent Hamiltonians whose
suspended vector fields are globally Lipschitz, with one-periodic orbits `x±` whose initial points
are nondegenerate fixed points of the time-one map, and let `u` be a `C¹` map whose loops converge
uniformly to `x₋` at `-∞` and to `x₊` at `+∞`, with slice defects `∂t u - X_{H±_t}(u)` tending
uniformly to zero at the ends. Let `μ ↦ (J_{i,μ}, K_{s,i,μ}, K_{t,i,μ})`, `i = 1, 2`, be two
paths of Floer data, jointly `C¹` in the parameter, the point of the cylinder and the target point
(with `C²` Hamiltonians), with `ω`-compatible almost complex structures, cylindrical near the ends
with end Hamiltonians `H±` for `μ ∈ [[a, b]]`, and with the same data at `μ = a` and at `μ = b`.
Then
transporting an orientation of the determinant line of `D_u` for the data at `a` to `b` along the
first path, and along the second path, gives the same orientation of the determinant line of
`D_u` for the data at `b`, once the determinant lines of the equal operators of the two paths at
`a` and at `b` are identified by `LinearMap.detLineCongrOfEq`.

The continuity and the Fredholm property of the two paths of operators, which orientation
transport needs, hold by `TauCeti.SymplecticForm.continuousOn_floerSobolevOperator_family` and
`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible`. -/
theorem detLineOrientationTransport_floerSobolevOperator_congr (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    {J₁ J₂ : ℝ × (ℝ × ℝ) → F → AlmostComplexStructure F} {Ks₁ Kt₁ Ks₂ Kt₂ : ℝ × (ℝ × ℝ) → F → ℝ}
    {Jm₁ Jp₁ Jm₂ Jp₂ : ℝ → ℝ → F → AlmostComplexStructure F} {Hm Hp : ℝ → F → ℝ} {R₁ R₂ : ℝ}
    {u : ℝ × ℝ → F} {a b : ℝ}
    (hcyl₁ : ∀ μ ∈ uIcc a b, Floer.IsCylindricalNearEnds (fun w ↦ J₁ (μ, w))
      (fun w ↦ Ks₁ (μ, w)) (fun w ↦ Kt₁ (μ, w)) (Jm₁ μ) (Jp₁ μ) Hm Hp R₁ u)
    (hcyl₂ : ∀ μ ∈ uIcc a b, Floer.IsCylindricalNearEnds (fun w ↦ J₂ (μ, w))
      (fun w ↦ Ks₂ (μ, w)) (fun w ↦ Kt₂ (μ, w)) (Jm₂ μ) (Jp₂ μ) Hm Hp R₂ u)
    (hJ₁ : ContDiff ℝ 1 fun p : (ℝ × (ℝ × ℝ)) × F ↦ (J₁ p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJ₂ : ContDiff ℝ 1 fun p : (ℝ × (ℝ × ℝ)) × F ↦ (J₂ p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs₁ : ContDiff ℝ 2 (uncurry Ks₁)) (hKt₁ : ContDiff ℝ 2 (uncurry Kt₁))
    (hKs₂ : ContDiff ℝ 2 (uncurry Ks₂)) (hKt₂ : ContDiff ℝ 2 (uncurry Kt₂))
    (hJc₁ : ∀ p y, ω.Compatible (J₁ p y)) (hJc₂ : ∀ p y, ω.Compatible (J₂ p y))
    (hu : ContDiff ℝ 1 u)
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1) {xm : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xp : ℝ → F}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t) (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (hJa : ∀ w, J₁ (a, w) = J₂ (a, w)) (hKsa : ∀ w, Ks₁ (a, w) = Ks₂ (a, w))
    (hKta : ∀ w, Kt₁ (a, w) = Kt₂ (a, w)) (hJb : ∀ w, J₁ (b, w) = J₂ (b, w))
    (hKsb : ∀ w, Ks₁ (b, w) = Ks₂ (b, w)) (hKtb : ∀ w, Kt₁ (b, w) = Kt₂ (b, w))
    (hT₁ : ContinuousOn (fun μ ↦ ω.floerSobolevOperator
      (fun w y ↦ (J₁ (μ, w) y).toLinearMap.toContinuousLinearMap) (fun w ↦ Ks₁ (μ, w))
      (fun w ↦ Kt₁ (μ, w)) u) (uIcc a b))
    (hF₁ : ∀ μ ∈ uIcc a b, (ω.floerSobolevOperator
      (fun w y ↦ (J₁ (μ, w) y).toLinearMap.toContinuousLinearMap) (fun w ↦ Ks₁ (μ, w))
      (fun w ↦ Kt₁ (μ, w)) u).IsFredholm)
    (hT₂ : ContinuousOn (fun μ ↦ ω.floerSobolevOperator
      (fun w y ↦ (J₂ (μ, w) y).toLinearMap.toContinuousLinearMap) (fun w ↦ Ks₂ (μ, w))
      (fun w ↦ Kt₂ (μ, w)) u) (uIcc a b))
    (hF₂ : ∀ μ ∈ uIcc a b, (ω.floerSobolevOperator
      (fun w y ↦ (J₂ (μ, w) y).toLinearMap.toContinuousLinearMap) (fun w ↦ Ks₂ (μ, w))
      (fun w ↦ Kt₂ (μ, w)) u).IsFredholm)
    :
    detLineOrientationTransport a b hT₂ hF₂ ∘
        Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [hJa, hKsa, hKta])) =
      Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [hJb, hKsb, hKtb])) ∘
        detLineOrientationTransport a b hT₁ hF₁ := by
  funext o
  -- The paths of almost complex structures are joined relative to the complex structure of `F`.
  have h₀ := ω.compatible_ofComplexModule_of_forall_eq_im_inner hω
  have hJt₁ (p : ℝ × (ℝ × ℝ)) (y : F) : ω.Tames (J₁ p y) := (hJc₁ p y).tames
  have hJt₂ (p : ℝ × (ℝ × ℝ)) (y : F) : ω.Tames (J₂ p y) := (hJc₂ p y).tames
  -- The homotopy of data from the first path (`σ = 0`) to the second (`σ = 1`) is `C¹` (with
  -- `C²` Hamiltonians), and cylindrical near the ends with the end Hamiltonians `H±` over the
  -- parameter rectangle.
  have hJH := contDiff_homotopyAlmostComplex (hJ₁ := hJt₁) (hJ₂ := hJt₂) h₀ hJ₁ hJ₂
  have hKsH := contDiff_homotopyHamiltonian hKs₁ hKs₂
  have hKtH := contDiff_homotopyHamiltonian hKt₁ hKt₂
  have hcyl (p : ℝ × ℝ) (hp : p ∈ uIcc 0 1 ×ˢ uIcc a b) :=
    isCylindricalNearEnds_homotopy (σ := p.1) h₀ (hcyl₁ p.2 hp.2) (hcyl₂ p.2 hp.2) hJH hKsH hKtH
  refine detLineOrientationTransport_eq_of_homotopy_of_eq (s₀ := 0) (s₁ := 1)
    (H := fun p ↦ ω.floerSobolevOperator
      (fun w y ↦ (homotopyAlmostComplex h₀ hJt₁ hJt₂ (p, w) y).toLinearMap.toContinuousLinearMap)
      (fun w ↦ homotopyHamiltonian Ks₁ Ks₂ (p, w)) (fun w ↦ homotopyHamiltonian Kt₁ Kt₂ (p, w)) u)
    ?_ ?_ ?_ ?_ ?_ ?_ hT₁ hF₁ hT₂ hF₂ _ _ o
  · exact ω.continuousOn_floerSobolevOperator_family hcyl hJH hKsH hKtH hu
      (continuous_iff_continuousAt.2 fun t ↦ (hxm t).continuousAt)
      (continuous_iff_continuousAt.2 fun t ↦ (hxp t).continuousAt) huxm hδm huxp hδp
  · exact fun p hp ↦ ω.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible hω (hcyl p hp)
      (contDiff_comp_prodMap_prodMk_right hJH p) (contDiff_comp_prodMap_prodMk_right hKsH p)
      (contDiff_comp_prodMap_prodMk_right hKtH p)
      (fun _ y ↦ compatible_homotopyAlmostComplex h₀ (hJc₁ _ y) (hJc₂ _ y)) hu hXm hHm hHmper hxm
      hxmper hndm huxm hδm hXp hHp hHpper hxp hxpper hndp huxp hδp
  · exact fun μ ↦ by simp only [homotopyAlmostComplex_zero, homotopyHamiltonian_zero]
  · exact fun μ ↦ by simp only [homotopyAlmostComplex_one, homotopyHamiltonian_one]
  · exact fun σ _ ↦ by
      simp only [homotopyAlmostComplex_of_eq h₀ _ (hJa _),
        homotopyHamiltonian_of_eq _ rfl (hKsa _).symm,
        homotopyHamiltonian_of_eq _ rfl (hKta _).symm]
  · exact fun σ _ ↦ by
      simp only [homotopyAlmostComplex_of_eq h₀ _ (hJb _),
        homotopyHamiltonian_of_eq _ rfl (hKsb _).symm,
        homotopyHamiltonian_of_eq _ rfl (hKtb _).symm]

/-- **Orientation transport around a loop of Floer data is trivial.** Under the hypotheses of
`TauCeti.SymplecticForm.detLineOrientationTransport_floerSobolevOperator_congr` on a single path
`μ ↦ (J_μ, K_{s,μ}, K_{t,μ})` of Floer data with the same data at `μ = a` and at `μ = b`,
transporting an orientation of the determinant line of `D_u` from `a` to `b` along the path is the
identification of the determinant lines of the equal operators at `a` and at `b`. So the
determinant lines of `D_u` are orientable over every loop of Floer data with fixed end
Hamiltonians. -/
theorem detLineOrientationTransport_floerSobolevOperator_eq_map (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    {J : ℝ × (ℝ × ℝ) → F → AlmostComplexStructure F} {Ks Kt : ℝ × (ℝ × ℝ) → F → ℝ}
    {Jm Jp : ℝ → ℝ → F → AlmostComplexStructure F} {Hm Hp : ℝ → F → ℝ} {R : ℝ}
    {u : ℝ × ℝ → F} {a b : ℝ}
    (hcyl : ∀ μ ∈ uIcc a b, Floer.IsCylindricalNearEnds (fun w ↦ J (μ, w))
      (fun w ↦ Ks (μ, w)) (fun w ↦ Kt (μ, w)) (Jm μ) (Jp μ) Hm Hp R u)
    (hJ : ContDiff ℝ 1 fun p : (ℝ × (ℝ × ℝ)) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJc : ∀ p y, ω.Compatible (J p y)) (hu : ContDiff ℝ 1 u)
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1) {xm : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xp : ℝ → F}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t) (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (hJab : ∀ w, J (a, w) = J (b, w)) (hKsab : ∀ w, Ks (a, w) = Ks (b, w))
    (hKtab : ∀ w, Kt (a, w) = Kt (b, w))
    (hT : ContinuousOn (fun μ ↦ ω.floerSobolevOperator
      (fun w y ↦ (J (μ, w) y).toLinearMap.toContinuousLinearMap) (fun w ↦ Ks (μ, w))
      (fun w ↦ Kt (μ, w)) u) (uIcc a b))
    (hF : ∀ μ ∈ uIcc a b, (ω.floerSobolevOperator
      (fun w y ↦ (J (μ, w) y).toLinearMap.toContinuousLinearMap) (fun w ↦ Ks (μ, w))
      (fun w ↦ Kt (μ, w)) u).IsFredholm) :
    ∀ o, detLineOrientationTransport a b hT hF o =
      Module.Ray.map (LinearMap.detLineCongrOfEq (by simp only [hJab, hKsab, hKtab])) o := by
  intro o
  have hT₀ := hF a left_mem_uIcc
  -- Compare the path with the constant path at the data at `a`, along which transport is the
  -- identity.
  have hg : ContDiff ℝ ⊤ fun p : (ℝ × (ℝ × ℝ)) × F ↦ ((a, p.1.2), p.2) :=
    (contDiff_const.prodMk contDiff_fst.snd).prodMk contDiff_snd
  have key := detLineOrientationTransport_floerSobolevOperator_congr ω hω
    (J₂ := fun p ↦ J (a, p.2)) (Ks₂ := fun p ↦ Ks (a, p.2)) (Kt₂ := fun p ↦ Kt (a, p.2))
    (Jm₂ := fun _ ↦ Jm a) (Jp₂ := fun _ ↦ Jp a) hcyl (fun _ _ ↦ hcyl a left_mem_uIcc) hJ
    (hJ.comp (hg.of_le le_top)) hKs hKt (hKs.comp (hg.of_le le_top)) (hKt.comp (hg.of_le le_top))
    hJc (fun p ↦ hJc (a, p.2)) hu hXm hHm hHmper hxm hxmper hndm huxm hδm hXp hHp hHpper hxp
    hxpper hndp huxp hδp (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun w ↦ (hJab w).symm)
    (fun w ↦ (hKsab w).symm) (fun w ↦ (hKtab w).symm) hT hF
    -- The operator of the constant path at `μ` is that at `a` once `(μ, w).2` reduces to `w`.
    (by dsimp only; exact continuousOn_const) (fun _ _ ↦ by dsimp only; exact hT₀)
  have := congrFun key o
  rw [Function.comp_apply, Function.comp_apply] at this
  -- Transport along the constant path is the identity; `erw` matches its operators, which are
  -- those at `a` only up to the reduction of `(μ, w).2` to `w`.
  erw [detLineOrientationTransport_const hT₀ a b, id] at this
  rw [← (Equiv.symm_apply_eq _).2 this, Module.Ray.map_symm, LinearMap.detLineCongrOfEq_symm]
  induction o using Module.Ray.ind with | h v hv => ?_
  simp only [Module.Ray.map_apply]
  congr 1
  rw [← LinearEquiv.trans_apply, LinearMap.detLineCongrOfEq_trans]

end Transport

end TauCeti.SymplecticForm
