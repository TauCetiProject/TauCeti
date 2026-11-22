/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.CircleResolution
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Sphere
public import TauCeti.Algebra.Homology.DG.Algebra.KoszulTwist
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Relative.Basic

/-!
# The semi-free resolution of the ground ring over the chains on the loops of a sphere

Brown's twisted tensor product resolves the ground ring `R` over the chains `C_*(Ω_b B; R)` on the
Moore loops of a CW complex `B` by a semi-free module with one free generator for each cell,
attached along a cycle representing the attaching map of the cell. For a complex with one `0`-cell
`e₀` at the base point and one `(n + 1)`-cell `e₁` attached along an `n`-cycle `x` of the Moore
loops, this module is

`K = C_*(Ω_b B; R) e₀ ⊕ C_*(Ω_b B; R) e₁`,  `D e₀ = 0`,  `D e₁ = x e₀`,

the free module of the cocycle `TauCeti.cycleCellCocycle R n x` of a cell attached along `x`, on
the generators `Unit ⊕ Unit` with `e₀ = Sum.inl ()` of index `0` and `e₁ = Sum.inr ()` of index
`n + 1`. The differential of a
vector `α e₀ + β e₁` is `dα + κ(β) x` on `e₀` and `dβ` on `e₁`, with `κ` the Koszul sign twist
(`TauCeti.cycleCellCocycle_differential_apply`). The cocycle of the circle,
`TauCeti.loopCellCocycle R γ`, has the same shape with `n = 0` and `x = [γ] - [1]`.

The augmentation `ε : K → R` takes the augmentation of the coefficient of `e₀`
(`TauCeti.loopCellAugmentation`); it vanishes on boundaries as soon as `x` has augmentation zero.
It is a quasi-isomorphism as soon as right multiplication by `x` is injective on homology and every
cycle of augmentation zero is, up to a boundary, a right multiple of `x` by a cycle
(`TauCeti.exists_cycleCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`): the module is
then a semi-free resolution of `R`.

For the sphere `Sⁿ`, `n = m + 2`, with one `0`-cell at the pole and one `n`-cell, the attaching
cycle `x` is the signed sum of the faces of the cube of Moore paths from the pole along the
characteristic map of the top cell (`TauCeti.sphereAttachingCycle`), an `(n - 1)`-cycle of the
Moore loops. Right multiplication by `x` is an isomorphism
`H_q(Ω_b Sⁿ) ≅ H_{q+n-1}(Ω_b Sⁿ)` (`TauCeti.sphereLoopHomologyMulRightEquiv`), the loops have no
homology in the degrees `1, …, n - 2` (`TauCeti.isZero_homology_sphereLoop`), and they form a path
connected space, since `Sⁿ` is simply connected. So both conditions hold
(`TauCeti.exists_cubicalChainDifferential_eq_of_eq_mul_sphereAttachingChain`,
`TauCeti.exists_mul_sphereAttachingChain_add_cubicalChainDifferential_eq`), and the module
of the sphere (`TauCeti.sphereCellCocycle`) is a semi-free resolution of the ground ring
over `C_*(Ω_b Sⁿ)`
(`TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`). For `S²` the
attaching cycle has dimension `1`.

The homological conditions are stated on all of the algebra `C_*(Ω_b B; R)`, a direct sum of the
chains of every dimension, and are proved for the sphere one dimension at a time. The passage uses
the components of the differential and of right multiplication by a homogeneous chain
(`TauCeti.cubicalChainDifferential_apply`, `TauCeti.mul_cubicalChainLof_apply_add`) and of the
augmentation (`TauCeti.loopChainAugmentation_eq_augment`).

## Main definitions

* `TauCeti.cycleCellCocycle R n x`: the twisting cocycle of one `(n + 1)`-cell attached along an
  `n`-cycle `x` to one `0`-cell.
* `TauCeti.sphereAttachingChain h k`: the attaching cycle of the top cell of the sphere, in the
  loop chain algebra.
* `TauCeti.sphereCellCocycle h k`: the cocycle of the top cell of the sphere.

## Main results

* `TauCeti.cycleCellCocycle_differential_apply`: the differential on `α e₀ + β e₁`.
* `TauCeti.exists_cycleCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`: the module
  resolves the ground ring when right multiplication by `x` behaves as for a sphere.
* `TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`: Brown's
  resolution of the ground ring over the chains on the loops of a sphere.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* R. Bott and H. Samelson, *On the Pontryagin product in spaces of paths*, Comment. Math. Helv. 27
  (1953), 320–337.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public noncomputable section

open CategoryTheory HomologicalComplex Metric

namespace TauCeti

/-! ### The cocycle of a cell attached along a cycle -/

section CycleCell

variable {B : Type*} [TopologicalSpace B] {b : B} (R : Type*) [CommRing R]

/-- **The twisting cocycle of one `(n + 1)`-cell attached along an `n`-cycle.** On the
generators `Unit ⊕ Unit`, the `0`-cell `e₀ = Sum.inl ()` of index `0` has zero row, and the cell
`e₁ = Sum.inr ()` of index `n + 1` is attached (`TauCeti.RowFiniteTwistingCocycle.attach`) along
the cycle `x e₀`, for an `n`-cycle `x` of the chains `C_*(Ω_b B; R)` on the Moore loops. For a
sphere and the cycle swept out by the boundary of its top cell, this is Brown's semi-free
resolution of `R` over `C_*(Ω_b B; R)`. -/
def cycleCellCocycle (n : ℕ) (x : loopChainAlgebra B b R)
    (hx : x ∈ cubicalChainGrading (MooreLoopSpace B b) R (-(n : ℤ)))
    (hdx : cubicalChainDifferential (MooreLoopSpace B b) R x = 0) :
    RowFiniteTwistingCocycle (R := R) (A := loopChainAlgebra B b R)
      (cubicalChainGrading (MooreLoopSpace B b) R) (cubicalChainDifferential (MooreLoopSpace B b) R)
      (Unit ⊕ Unit) (Sum.elim (fun _ ↦ 0) (fun _ ↦ (n : ℤ) + 1)) :=
  (0 : RowFiniteTwistingCocycle (R := R) (A := loopChainAlgebra B b R)
      (cubicalChainGrading (MooreLoopSpace B b) R) (cubicalChainDifferential (MooreLoopSpace B b) R)
      Unit (fun _ ↦ 0)).attach
    (fun _ ↦ Finsupp.single () x)
    (fun _ y ↦ by
      cases y
      simpa [show (0 : ℤ) - (n + 1) + 1 = -n by ring] using hx)
    (fun _ ↦ by
      rw [RowFiniteTwistingCocycle.zero_m, rowFiniteTwistedDifferential_zero,
        Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, hdx, Finsupp.single_zero])

variable {R} {n : ℕ} {x : loopChainAlgebra B b R}
  (hx : x ∈ cubicalChainGrading (MooreLoopSpace B b) R (-(n : ℤ)))
  (hdx : cubicalChainDifferential (MooreLoopSpace B b) R x = 0)

@[simp]
theorem cycleCellCocycle_m_inl : (cycleCellCocycle R n x hx hdx).m (Sum.inl ()) = 0 := by
  simp [cycleCellCocycle]

/-- The row of `e₁` is `x e₀`. -/
@[simp]
theorem cycleCellCocycle_m_inr :
    (cycleCellCocycle R n x hx hdx).m (Sum.inr ()) = Finsupp.single (Sum.inl ()) x := by
  rw [cycleCellCocycle, RowFiniteTwistingCocycle.attach_m_inr, Finsupp.mapDomain_single]

/-- The cocycle is one-sided, so its free module is semi-free
(`TauCeti.RowFiniteTwistingCocycle.wellFounded_mem_support`). -/
theorem cycleCellCocycle_m_eq_zero_of_le {y z : Unit ⊕ Unit}
    (h : Sum.elim (fun _ ↦ (0 : ℤ)) (fun _ ↦ (n : ℤ) + 1) y ≤
      Sum.elim (fun _ ↦ (0 : ℤ)) (fun _ ↦ (n : ℤ) + 1) z) :
    (cycleCellCocycle R n x hx hdx).m y z = 0 :=
  RowFiniteTwistingCocycle.attach_m_eq_zero_of_le _ _ _ (fun _ _ _ ↦ by simp)
    (fun _ _ h ↦ absurd h (by simp)) y z h

/-- The differential of the free module of `TauCeti.cycleCellCocycle R n x` on `α e₀ + β e₁`: the
coefficient of `e₀` is `dα + κ(β) x`, with `κ` the Koszul sign twist, and the coefficient of `e₁`
is `dβ`. -/
theorem cycleCellCocycle_differential_apply (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m u =
      Finsupp.single (Sum.inl ())
          (cubicalChainDifferential (MooreLoopSpace B b) R (u (Sum.inl ())) +
          (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist
              1 (u (Sum.inr ())) * x) +
        Finsupp.single (Sum.inr ())
          (cubicalChainDifferential (MooreLoopSpace B b) R (u (Sum.inr ()))) := by
  have hu : u = Finsupp.single (Sum.inl ()) (u (Sum.inl ())) +
      Finsupp.single (Sum.inr ()) (u (Sum.inr ())) := by
    ext i
    rcases i with ⟨⟩ | ⟨⟩ <;> simp
  conv_lhs => rw [hu]
  rw [map_add, rowFiniteTwistedDifferential_single_koszulTwist,
    rowFiniteTwistedDifferential_single_koszulTwist, cycleCellCocycle_m_inl, cycleCellCocycle_m_inr,
    smul_zero, add_zero, Finsupp.smul_single, smul_eq_mul, Finsupp.single_add]
  abel

/-- The coefficient of `e₀` in the differential of `u` is `d(u e₀) + κ(u e₁) x`. -/
@[simp]
theorem cycleCellCocycle_differential_apply_inl (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m u
          (Sum.inl ()) =
      cubicalChainDifferential (MooreLoopSpace B b) R (u (Sum.inl ())) +
        (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist
            1 (u (Sum.inr ())) * x := by
  simp [cycleCellCocycle_differential_apply]

/-- The coefficient of `e₁` in the differential of `u` is `d(u e₁)`. -/
@[simp]
theorem cycleCellCocycle_differential_apply_inr (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m u
          (Sum.inr ()) =
      cubicalChainDifferential (MooreLoopSpace B b) R (u (Sum.inr ())) := by
  simp [cycleCellCocycle_differential_apply]

/-- The differential of `α e₀` is `(dα) e₀`. -/
@[simp]
theorem cycleCellCocycle_differential_single_inl (α : loopChainAlgebra B b R) :
    rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m
        (Finsupp.single (Sum.inl ()) α) =
      Finsupp.single (Sum.inl ()) (cubicalChainDifferential (MooreLoopSpace B b) R α) := by
  simp [cycleCellCocycle_differential_apply]

/-- The differential of `β e₁` is `κ(β) x e₀ + (dβ) e₁`, with `κ` the Koszul sign twist. -/
theorem cycleCellCocycle_differential_single_inr (β : loopChainAlgebra B b R) :
    rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m
        (Finsupp.single (Sum.inr ()) β) =
      Finsupp.single (Sum.inl ())
          ((InternalGrading.ofDecomposition
              (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist 1 β * x) +
        Finsupp.single (Sum.inr ()) (cubicalChainDifferential (MooreLoopSpace B b) R β) := by
  simp [cycleCellCocycle_differential_apply]

/-- When the attaching cycle has augmentation zero, as it does in positive dimension, the
augmentation of the free module of `TauCeti.cycleCellCocycle R n x` vanishes on boundaries. -/
theorem loopCellAugmentation_cycleCellCocycle_differential
    (hεx : loopChainAugmentation B b R x = 0) (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    loopCellAugmentation B b R
        (rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R)
          (cycleCellCocycle R n x hx hdx).m u) = 0 := by
  simp [loopCellAugmentation_apply, hεx]

/-- A cycle `α` of augmentation zero which is, up to a boundary, a right multiple `β x` of a cycle
`β` gives a boundary `α e₀` of the free module of `TauCeti.cycleCellCocycle R n x`: if
`α = β x + d w`, then `α e₀` is the boundary of `w e₀ + κ(β) e₁`. -/
private theorem exists_cycleCellCocycle_differential_eq_single_inl {α β w : loopChainAlgebra B b R}
    (hβ : cubicalChainDifferential (MooreLoopSpace B b) R β = 0)
    (hα : β * x + cubicalChainDifferential (MooreLoopSpace B b) R w = α) :
    ∃ v, rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m v =
        Finsupp.single (Sum.inl ()) α := by
  have hdκ : cubicalChainDifferential (MooreLoopSpace B b) R
      ((InternalGrading.ofDecomposition
        (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist 1 β) = 0 := by
    rw [← neg_eq_zero, ← (loopChain_isDGAlgebra B b R).toIsNonUnitalDGAlgebra.koszulTwist_map,
      hβ, map_zero]
  refine ⟨Finsupp.single (Sum.inl ()) w + Finsupp.single (Sum.inr ())
    ((InternalGrading.ofDecomposition
      (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist 1 β), ?_⟩
  rw [map_add, cycleCellCocycle_differential_single_inl, cycleCellCocycle_differential_single_inr,
    InternalGrading.koszulTwist_koszulTwist, hdκ, Finsupp.single_zero, add_zero,
    ← Finsupp.single_add, add_comm, hα]

/-- **The module of a cell attached along a cycle resolves the ground ring** when right
multiplication by the attaching cycle `x` behaves as for a sphere: a cycle `β` with `β x` a
boundary is a boundary, and every cycle of augmentation zero is the sum of a right multiple `β x`
of a cycle `β` and a boundary. Then every cycle of the free module of
`TauCeti.cycleCellCocycle R n x` whose augmentation vanishes is a boundary. Since the augmentation
vanishes on boundaries (`TauCeti.loopCellAugmentation_cycleCellCocycle_differential`) and takes
the value `1` on the cycle `e₀`, it is a quasi-isomorphism onto `R`. -/
theorem exists_cycleCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero
    (hεx : loopChainAugmentation B b R x = 0)
    (hinj : ∀ β w : loopChainAlgebra B b R,
      cubicalChainDifferential (MooreLoopSpace B b) R β = 0 →
      cubicalChainDifferential (MooreLoopSpace B b) R w = β * x →
      ∃ γ, cubicalChainDifferential (MooreLoopSpace B b) R γ = β)
    (hsurj : ∀ α : loopChainAlgebra B b R,
      cubicalChainDifferential (MooreLoopSpace B b) R α = 0 →
      loopChainAugmentation B b R α = 0 → ∃ β w : loopChainAlgebra B b R,
        cubicalChainDifferential (MooreLoopSpace B b) R β = 0 ∧
        β * x + cubicalChainDifferential (MooreLoopSpace B b) R w = α)
    {u : Unit ⊕ Unit →₀ loopChainAlgebra B b R}
    (hu : rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m u =
        0)
    (hε : loopCellAugmentation B b R u = 0) :
    ∃ v, rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m v =
        u := by
  set D := rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
    (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
    (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m with hD
  -- The Koszul twist `κ` anticommutes with the differential.
  have hdκ (a : loopChainAlgebra B b R) :
      cubicalChainDifferential (MooreLoopSpace B b) R
        ((InternalGrading.ofDecomposition
          (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist 1 a) =
        -(InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist
          1 (cubicalChainDifferential (MooreLoopSpace B b) R a) := by
    rw [(loopChain_isDGAlgebra B b R).toIsNonUnitalDGAlgebra.koszulTwist_map, neg_neg]
  have hu0 := congrArg (· (Sum.inl ())) hu
  have hu1 := congrArg (· (Sum.inr ())) hu
  simp only [hD, cycleCellCocycle_differential_apply_inl, cycleCellCocycle_differential_apply_inr,
    Finsupp.coe_zero, Pi.zero_apply] at hu0 hu1
  -- The coefficient `β` of `e₁` is a cycle with `κ(β) x` a boundary, so `κ(β) = dγ`.
  obtain ⟨γ, hγ⟩ := hinj _ (-u (Sum.inl ())) (by rw [hdκ, hu1, map_zero, neg_zero])
    (by rw [map_neg]; exact neg_eq_of_add_eq_zero_right hu0)
  -- Subtracting the boundary of `-κ(γ) e₁` leaves a cycle `w` supported on `e₀`.
  set w := u - D (Finsupp.single (Sum.inr ()) (-(InternalGrading.ofDecomposition
    (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist 1 γ)) with hw
  have hw1 : w (Sum.inr ()) = 0 := by
    simp [hw, hD, cycleCellCocycle_differential_single_inr, hdκ, hγ,
      InternalGrading.koszulTwist_koszulTwist]
  have hw' : w = Finsupp.single (Sum.inl ()) (w (Sum.inl ())) := by
    ext i
    rcases i with ⟨⟩ | ⟨⟩ <;> simp [hw1]
  have hdw : cubicalChainDifferential (MooreLoopSpace B b) R (w (Sum.inl ())) = 0 := by
    have hDw : D w = 0 := by
      rw [hw, map_sub, hu, (cycleCellCocycle R n x hx hdx).differential_sq_zero
        (loopChain_isDGAlgebra B b R), sub_zero]
    have := congrArg (· (Sum.inl ())) hDw
    rw [hw', hD, cycleCellCocycle_differential_single_inl] at this
    simpa using this
  have hεw : loopChainAugmentation B b R (w (Sum.inl ())) = 0 := by
    rw [← loopCellAugmentation_apply, hw, map_sub, hε, hD,
      loopCellAugmentation_cycleCellCocycle_differential hx hdx hεx, sub_zero]
  -- The cycle `w e₀` of augmentation zero is a boundary.
  obtain ⟨β', w', hβ', hβw'⟩ := hsurj _ hdw hεw
  obtain ⟨v, hv⟩ := exists_cycleCellCocycle_differential_eq_single_inl hx hdx hβ' hβw'
  rw [← hD] at hv
  refine ⟨Finsupp.single (Sum.inr ()) (-(InternalGrading.ofDecomposition
    (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist 1 γ) + v, ?_⟩
  rw [map_add, hv, ← hw', hw]
  abel

end CycleCell

/-! ### The sphere -/

section Sphere

variable {ι : Type} [Fintype ι] {m : ℕ} (h : Fintype.card ι = m + 3) (k : Type) [CommRing k]

local notation "Sph" => sphere (0 : EuclideanSpace ℝ ι) 1

/-- The attaching cycle of the top cell of the sphere, as a normalized cubical chain of the Moore
loops at the pole. -/
private def sphereAttachingCycleChain :
    NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (m + 1) :=
  (((normalizedCubicalChainComplex k).obj _).iCycles (m + 1)).hom (sphereAttachingCycle h k)

/-- The **attaching cycle of the top cell of the sphere** `Sⁿ`, `n = m + 2`, as an element of the
loop chain algebra `C_*(Ω_b Sⁿ; k)`: the `(m + 1)`-cycle `TauCeti.sphereAttachingCycle`, the
signed sum of the faces of the cube of Moore paths from the pole along the top cell. -/
def sphereAttachingChain : loopChainAlgebra Sph (spherePolePoint h) k :=
  cubicalChainLof (MooreLoopSpace Sph (spherePolePoint h)) k (m + 1) (sphereAttachingCycleChain h k)

/-- The attaching chain is the image of the attaching cycle in the loop chain algebra. -/
theorem sphereAttachingChain_def :
    sphereAttachingChain h k = cubicalChainLof (MooreLoopSpace Sph (spherePolePoint h)) k (m + 1)
      ((((normalizedCubicalChainComplex k).obj _).iCycles (m + 1)).hom
        (sphereAttachingCycle h k)) :=
  (rfl)

/-- The attaching cycle has dimension `m + 1`. -/
theorem sphereAttachingChain_mem :
    sphereAttachingChain h k ∈
      cubicalChainGrading (MooreLoopSpace Sph (spherePolePoint h)) k (-((m + 1 : ℕ) : ℤ)) :=
  cubicalChainLof_mem _ _ _

/-- The attaching cycle is a cycle. -/
theorem cubicalChainDifferential_sphereAttachingChain :
    cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (sphereAttachingChain h k) = 0 :=
  cubicalChainDifferential_lof_iCycles (Y := MooreLoopSpace Sph (spherePolePoint h)) (m + 1)
    (sphereAttachingCycle h k)

/-- The attaching cycle has augmentation zero, being of positive dimension. -/
theorem loopChainAugmentation_sphereAttachingChain :
    loopChainAugmentation Sph (spherePolePoint h) k (sphereAttachingChain h k) = 0 :=
  loopChainAugmentation_lof_succ _ _

/-- **Brown's cocycle of the sphere** `Sⁿ`, `n = m + 2`: one `0`-cell at the pole and
one `n`-cell attached along the attaching cycle `TauCeti.sphereAttachingChain h k`. Its free
module is a semi-free resolution of `k` over `C_*(Ω_b Sⁿ; k)`
(`TauCeti.exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`). -/
def sphereCellCocycle :
    RowFiniteTwistingCocycle (R := k) (A := loopChainAlgebra Sph (spherePolePoint h) k)
      (cubicalChainGrading (MooreLoopSpace Sph (spherePolePoint h)) k)
      (cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k)
      (Unit ⊕ Unit) (Sum.elim (fun _ ↦ 0) (fun _ ↦ ((m + 1 : ℕ) : ℤ) + 1)) :=
  cycleCellCocycle k (m + 1) (sphereAttachingChain h k) (sphereAttachingChain_mem h k)
    (cubicalChainDifferential_sphereAttachingChain h k)

theorem sphereCellCocycle_def :
    sphereCellCocycle h k = cycleCellCocycle k (m + 1) (sphereAttachingChain h k)
      (sphereAttachingChain_mem h k) (cubicalChainDifferential_sphereAttachingChain h k) :=
  (rfl)

/-- A cycle `y` of dimension `j` of the loops of the sphere whose product with the attaching
cycle is a boundary is a boundary, since right multiplication by the attaching class is injective
on homology. -/
private theorem exists_boundary_eq_of_boundary_eq_mul {j : ℕ}
    {y : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k j}
    (hy : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (cubicalChainLof _ k j y) = 0)
    {w : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (j + (m + 1) + 1)}
    (hw : NormalizedCubicalChain.boundary _ k (j + (m + 1)) w =
      NormalizedCubicalChain.mul _ k j (m + 1) y (sphereAttachingCycleChain h k)) :
    ∃ y' : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (j + 1),
      NormalizedCubicalChain.boundary _ k j y' = y := by
  let X := TopCat.of (MooreLoopSpace Sph (spherePolePoint h))
  let K := (normalizedCubicalChainComplex k).obj X
  obtain ⟨z, hz⟩ := exists_iCycles_eq_of_cubicalChainDifferential_lof_eq_zero j hy
  have hdw : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (cubicalChainLof _ k (j + (m + 1)) (NormalizedCubicalChain.boundary _ k (j + (m + 1)) w)) =
        0 := by
    rw [← cubicalChainDifferential_lof_succ]
    exact (loopChain_isDGAlgebra Sph (spherePolePoint h) k).sq_zero _
  obtain ⟨wc, hwc⟩ := exists_iCycles_eq_of_cubicalChainDifferential_lof_eq_zero _ hdw
  -- The class of the product vanishes, so the class of `y` does.
  have hπw : K.homologyπ (j + (m + 1)) wc = 0 := by
    refine (K.moduleCat_homologyπ_eq_of_iCycles_sub_eq_d (w := 0) (m := j + (m + 1) + 1) w
      ?_).trans (map_zero _)
    rw [map_zero, sub_zero]
    exact hwc.trans (normalizedCubicalChainComplexXEquiv_d_apply X (j + (m + 1)) w).symm
  have hπz : K.homologyπ j z = 0 := by
    apply (sphereLoopHomologyMulRightEquiv h k j).injective
    rw [map_zero, sphereLoopHomologyMulRightEquiv_homologyπ h k j z wc
      (hwc.trans (hw.trans (congrArg (fun t ↦ NormalizedCubicalChain.mul _ k j (m + 1) t
        (sphereAttachingCycleChain h k)) hz.symm)))]
    exact hπw
  obtain ⟨y', hy'⟩ := (K.moduleCat_homologyπ_eq_zero_iff (m := j + 1) (by simp) z).1 hπz
  have hdy' : K.d (j + 1) j y' = K.iCycles j z := by
    rw [← hy', moduleCat_iCycles_toCycles_apply]
  exact ⟨y', (normalizedCubicalChainComplexXEquiv_d_apply X j y').symm.trans
    ((congrArg (normalizedCubicalChainComplexXEquiv X j) hdy').trans hz)⟩

/-- **Right multiplication by the attaching cycle of the sphere is injective on homology**: a
cycle `β` of the loop chain algebra of `Sⁿ` such that `β x` is a boundary is a boundary. -/
theorem exists_cubicalChainDifferential_eq_of_eq_mul_sphereAttachingChain
    {β w : loopChainAlgebra Sph (spherePolePoint h) k}
    (hβ : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k β = 0)
    (hw : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k w =
      β * sphereAttachingChain h k) :
    ∃ γ, cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k γ = β := by
  classical
  -- Each component `β j` is the boundary of some `γ j`.
  have key (j : ℕ) : ∃ y' : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k
      (j + 1), NormalizedCubicalChain.boundary _ k j y' = β j := by
    refine exists_boundary_eq_of_boundary_eq_mul h k
      (cubicalChainDifferential_lof_apply_eq_zero hβ j) (w := w (j + (m + 1) + 1)) ?_
    rw [← cubicalChainDifferential_apply, hw, sphereAttachingChain, mul_cubicalChainLof_apply_add]
  choose γ hγ using key
  refine ⟨∑ j ∈ β.support, cubicalChainLof _ k (j + 1) (γ j), ?_⟩
  rw [map_sum]
  conv_rhs => rw [← DirectSum.sum_support_of β]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [cubicalChainDifferential_lof_succ, hγ, DirectSum.lof_eq_of]

/-- A cycle of dimension zero of the loops of the sphere with augmentation zero is a boundary: the
sphere is simply connected, so its loops form a path connected space. -/
private theorem exists_boundary_eq_of_augment_eq_zero
    {a : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k 0}
    (ha : NormalizedCubicalChain.augment _ k a = 0) :
    ∃ w : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k 1,
      NormalizedCubicalChain.boundary _ k 0 w = a := by
  have : SimplyConnectedSpace Sph :=
    simplyConnectedSpace_sphere_of_lt_finrank (by simp [finrank_euclideanSpace, h]) 0 zero_le_one
  have hT : loopZeroChainToGroupAlgebra Sph (spherePolePoint h) k a = 0 := by
    have hker : loopZeroChainToGroupAlgebra Sph (spherePolePoint h) k a ∈
        RingHom.ker (MonoidAlgebra.augmentation k (FundamentalGroup Sph (spherePolePoint h))) := by
      rw [RingHom.mem_ker, ← loopChainToGroupAlgebra_lof_zero, augmentation_loopChainToGroupAlgebra,
        loopChainAugmentation_lof_zero, ha]
    rwa [MonoidAlgebra.ker_augmentation_eq_span_of_closure_eq_top k (s := ∅)
      (Subsingleton.elim _ _), Set.image_empty, Ideal.span_empty, Ideal.mem_bot] at hker
  exact (loopZeroChainToGroupAlgebra_eq_zero_iff a).1 hT

/-- A cycle of dimension `i + 1 ≤ m` of the loops of the sphere is a boundary. -/
private theorem exists_boundary_eq_of_lt {i : ℕ} (hi : i < m)
    {a : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (i + 1)}
    (ha : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (cubicalChainLof _ k (i + 1) a) = 0) :
    ∃ w : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (i + 2),
      NormalizedCubicalChain.boundary _ k (i + 1) w = a := by
  rw [cubicalChainDifferential_lof_succ] at ha
  exact NormalizedCubicalChain.exists_boundary_eq_of_isZero_homology
    (X := TopCat.of (MooreLoopSpace Sph (spherePolePoint h))) (isZero_homology_sphereLoop h k hi)
    (DirectSum.of_injective (β := fun n ↦ NormalizedCubicalChain _ k n) i
      (by simpa [DirectSum.lof_eq_of] using ha))

/-- A cycle `a` of dimension `i + m + 1` of the loops of the sphere is, up to a boundary, the
product `y x` of a cycle `y` of dimension `i` with the attaching cycle, since right
multiplication by the attaching class is onto on homology. -/
private theorem exists_mul_add_boundary_eq {i : ℕ}
    {a : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (i + (m + 1))}
    (ha : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (cubicalChainLof _ k (i + (m + 1)) a) = 0) :
    ∃ (y : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k i)
      (c : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k (i + (m + 1) + 1)),
      cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
        (cubicalChainLof _ k i y) = 0 ∧
      NormalizedCubicalChain.mul _ k i (m + 1) y (sphereAttachingCycleChain h k) +
        NormalizedCubicalChain.boundary _ k (i + (m + 1)) c = a := by
  let X := TopCat.of (MooreLoopSpace Sph (spherePolePoint h))
  let K := (normalizedCubicalChainComplex k).obj X
  obtain ⟨z, hz⟩ := exists_iCycles_eq_of_cubicalChainDifferential_lof_eq_zero _ ha
  -- A cycle `y` of dimension `i` whose product with the attaching class is the class of `a`.
  obtain ⟨z', hz'⟩ := K.moduleCat_homologyπ_surjective i
    ((sphereLoopHomologyMulRightEquiv h k i).symm (K.homologyπ (i + (m + 1)) z))
  obtain ⟨y, hy⟩ : ∃ y : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k i,
      normalizedCubicalChainComplexXEquiv X i (K.iCycles i z') = y := ⟨_, rfl⟩
  have hdy : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (cubicalChainLof _ k i y) = 0 :=
    hy ▸ cubicalChainDifferential_lof_iCycles i z'
  have hdp : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k
      (cubicalChainLof _ k (i + (m + 1))
        (NormalizedCubicalChain.mul _ k i (m + 1) y (sphereAttachingCycleChain h k))) = 0 := by
    rw [← cubicalChainLof_mul, ← sphereAttachingChain,
      (loopChain_isDGAlgebra Sph (spherePolePoint h) k).leibniz (cubicalChainLof_mem _ _ _), hdy,
      cubicalChainDifferential_sphereAttachingChain, zero_mul, mul_zero, smul_zero, add_zero]
  obtain ⟨wc, hwc⟩ := exists_iCycles_eq_of_cubicalChainDifferential_lof_eq_zero _ hdp
  have hπ : K.homologyπ (i + (m + 1)) wc = K.homologyπ (i + (m + 1)) z := by
    rw [← sphereLoopHomologyMulRightEquiv_homologyπ h k i z' wc
      (hwc.trans (congrArg (fun t ↦ NormalizedCubicalChain.mul _ k i (m + 1) t
        (sphereAttachingCycleChain h k)) hy.symm)), hz', LinearEquiv.apply_symm_apply]
  obtain ⟨c, hc⟩ := (K.moduleCat_homologyπ_eq_iff (m := i + (m + 1) + 1) (by simp) wc z).1 hπ
  obtain ⟨c', hc'⟩ : ∃ c' : NormalizedCubicalChain (MooreLoopSpace Sph (spherePolePoint h)) k
      (i + (m + 1) + 1), normalizedCubicalChainComplexXEquiv X _ c = c' := ⟨_, rfl⟩
  have hbc : NormalizedCubicalChain.boundary (MooreLoopSpace Sph (spherePolePoint h)) k
      (i + (m + 1)) c' =
        NormalizedCubicalChain.mul _ k i (m + 1) y (sphereAttachingCycleChain h k) - a :=
    (congrArg _ hc'.symm).trans ((normalizedCubicalChainComplexXEquiv_d_apply X _ c).symm.trans
      ((congrArg (normalizedCubicalChainComplexXEquiv X _) hc).trans (congrArg₂ (· - ·) hwc hz)))
  refine ⟨y, -c', hdy, ?_⟩
  rw [map_neg, hbc]
  abel

/-- **Cycles of the loops of the sphere are right multiples of the attaching cycle**: every cycle
`α` of the loop chain algebra of `Sⁿ` with augmentation zero is `β x + d w` for a cycle `β`. -/
theorem exists_mul_sphereAttachingChain_add_cubicalChainDifferential_eq
    {α : loopChainAlgebra Sph (spherePolePoint h) k}
    (hα : cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k α = 0)
    (hε : loopChainAugmentation Sph (spherePolePoint h) k α = 0) :
    ∃ β w : loopChainAlgebra Sph (spherePolePoint h) k,
      cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k β = 0 ∧
      β * sphereAttachingChain h k +
        cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k w = α := by
  classical
  -- Each homogeneous component of `α` is `β x + d w`.
  have key (j : ℕ) : ∃ β w : loopChainAlgebra Sph (spherePolePoint h) k,
      cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k β = 0 ∧
      β * sphereAttachingChain h k +
        cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k w =
          cubicalChainLof _ k j (α j) := by
    have hj := cubicalChainDifferential_lof_apply_eq_zero hα j
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · obtain ⟨w, hw⟩ := exists_boundary_eq_of_augment_eq_zero h k
        ((loopChainAugmentation_eq_augment α).symm.trans hε)
      exact ⟨0, cubicalChainLof _ k 1 w, map_zero _, by
        rw [zero_mul, zero_add, cubicalChainDifferential_lof_succ, hw]⟩
    by_cases hjm : j ≤ m
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨w, hw⟩ := exists_boundary_eq_of_lt h k (by omega) hj
      exact ⟨0, cubicalChainLof _ k (i + 2) w, map_zero _, by
        rw [zero_mul, zero_add, cubicalChainDifferential_lof_succ, hw]⟩
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + (m + 1) := ⟨j - (m + 1), by omega⟩
      obtain ⟨y, c, hy, hyc⟩ := exists_mul_add_boundary_eq h k hj
      exact ⟨cubicalChainLof _ k i y, cubicalChainLof _ k (i + (m + 1) + 1) c, hy, by
        rw [sphereAttachingChain, cubicalChainLof_mul, cubicalChainDifferential_lof_succ,
          ← map_add, hyc]⟩
  choose β w hβ hw using key
  refine ⟨∑ j ∈ α.support, β j, ∑ j ∈ α.support, w j,
    by rw [map_sum]; exact Finset.sum_eq_zero fun j _ ↦ hβ j, ?_⟩
  rw [Finset.sum_mul, map_sum, ← Finset.sum_add_distrib]
  conv_rhs => rw [← DirectSum.sum_support_of α]
  exact Finset.sum_congr rfl fun j _ ↦ (hw j).trans (DirectSum.lof_eq_of _ _ _ _ _)

/-- **Brown's resolution of the ground ring over the chains on the loops of a sphere.** For the
sphere `Sⁿ`, `n = m + 2`, with one `0`-cell at the pole and one `n`-cell attached along the
attaching cycle `x` of its top cell, every cycle of the free module of
`TauCeti.sphereCellCocycle h k` whose augmentation vanishes is a boundary. Since the augmentation
vanishes on boundaries and takes the value `1` on the cycle `e₀`, it is a quasi-isomorphism onto
`k`: the module `C_*(Ω_b Sⁿ; k) e₀ ⊕ C_*(Ω_b Sⁿ; k) e₁` with `D e₁ = x e₀` is a semi-free
resolution of `k` over the chains `C_*(Ω_b Sⁿ; k)` on the Moore loops. -/
theorem exists_sphereCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero
    {u : Unit ⊕ Unit →₀ loopChainAlgebra Sph (spherePolePoint h) k}
    (hu : rowFiniteTwistedDifferential (R := k) (A := loopChainAlgebra Sph (spherePolePoint h) k)
      (𝒜 := cubicalChainGrading (MooreLoopSpace Sph (spherePolePoint h)) k)
      (d := cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k)
      (sphereCellCocycle h k).m u = 0)
    (hε : loopCellAugmentation Sph (spherePolePoint h) k u = 0) :
    ∃ v, rowFiniteTwistedDifferential (R := k) (A := loopChainAlgebra Sph (spherePolePoint h) k)
      (𝒜 := cubicalChainGrading (MooreLoopSpace Sph (spherePolePoint h)) k)
      (d := cubicalChainDifferential (MooreLoopSpace Sph (spherePolePoint h)) k)
      (sphereCellCocycle h k).m v = u :=
  exists_cycleCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero _ _
    (loopChainAugmentation_sphereAttachingChain h k)
    (fun _ _ hβ hw ↦
      exists_cubicalChainDifferential_eq_of_eq_mul_sphereAttachingChain
        h k hβ hw)
    (fun _ hα hε ↦ exists_mul_sphereAttachingChain_add_cubicalChainDifferential_eq h k hα hε)
    hu hε

end Sphere

end TauCeti
