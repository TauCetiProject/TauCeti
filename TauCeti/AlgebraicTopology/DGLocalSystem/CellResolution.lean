/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.Algebra.Homology.DG.Algebra.KoszulTwist
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.Basic
public import TauCeti.Algebra.Homology.DG.Twisted.TwoGenerators

/-!
# The semi-free module of a cell attached along a cycle of the loops

Brown's twisted tensor product resolves the ground ring `R` over the chains `C_*(Ω_b B; R)` on the
Moore loops of a CW complex `B` by a semi-free module with one free generator for each cell,
attached along a cycle representing the attaching map of the cell. For a complex with one `0`-cell
`e₀` at the base point and one `(n + 1)`-cell `e₁` attached along an `n`-cycle `x` of the Moore
loops, this module is

`K = C_*(Ω_b B; R) e₀ ⊕ C_*(Ω_b B; R) e₁`,  `D e₀ = 0`,  `D e₁ = x e₀`.

As a row-finite twisting cocycle on the generators `Unit ⊕ Unit`, with `e₀ = Sum.inl ()` of index
`0` and `e₁ = Sum.inr ()` of index `n + 1`, this is `TauCeti.cycleCellCocycle R n x`: the generator
`e₁` is attached (`TauCeti.RowFiniteTwistingCocycle.attach`) along the cycle `x e₀` to the free
module on `e₀` with zero differential (`TauCeti.cycleCellCocycle_m_inr`). It is one-sided, so the
module is semi-free (`TauCeti.cycleCellCocycle_m_eq_zero_of_le`). The differential of a vector
`α e₀ + β e₁` is `dα ± β x` on `e₀` and `dβ` on `e₁`
(`TauCeti.cycleCellCocycle_differential_apply`).

The augmentation `ε : K → R` takes the augmentation of the coefficient of `e₀`
(`TauCeti.loopCellAugmentation`). It is linear over the augmentation of the loop chain algebra
(`TauCeti.loopCellAugmentation_smul`), vanishes on boundaries when `x` has augmentation zero
(`TauCeti.loopCellAugmentation_cycleCellCocycle_differential`) and takes the value `1` on the
cycle `e₀`. It is then a quasi-isomorphism as soon as right multiplication by `x` is injective on
homology and every cycle of augmentation zero is, up to a boundary, a right multiple of `x` by a
cycle (`TauCeti.exists_cycleCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`): the
module is then a semi-free resolution of `R`. The circle (`CircleResolution.lean`, with `n = 0`
and `x = [γ] - [1]`) and the spheres of dimension at least two (`SphereResolution.lean`) are
instances.

Any twisting cocycle `m` over the loop chains on two generators `p` and `q` with `ind q < ind p`,
such as the Barraud–Cornea cocycle of a Morse function with two critical points, has as twisted
complex the free module of `TauCeti.cycleCellCocycle R n (m p q)`, with `q` as `e₀` and `p` as
`e₁`. So its cycles of augmentation zero are boundaries as soon as those of the cell module are
(`TauCeti.exists_twistedDifferential_eq_of_cycleCellCocycle`).

## Main definitions

* `TauCeti.cycleCellCocycle R n x`: the twisting cocycle of one `(n + 1)`-cell attached along an
  `n`-cycle `x` to one `0`-cell.
* `TauCeti.loopCellAugmentation B b R`: the augmentation of its free module.

## Main results

* `TauCeti.cycleCellCocycle_differential_apply`: the differential on `α e₀ + β e₁`.
* `TauCeti.exists_cycleCellCocycle_differential_eq_of_loopCellAugmentation_eq_zero`: the module
  of a cell attached along `x` resolves the ground ring when right multiplication by `x` behaves
  as for a sphere.
* `TauCeti.exists_twistedDifferential_eq_of_cycleCellCocycle`: the same then holds for the twisted
  complex of a twisting cocycle on two generators whose entry is `x`.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public noncomputable section

open AlgebraicTopology

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
    (fun _ ↦ by simp [hdx])

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

/-- The row relation of the cocycle is well-founded, so its free module is semi-free. -/
theorem wellFounded_mem_support_cycleCellCocycle :
    WellFounded fun y z ↦ y ∈ ((cycleCellCocycle R n x hx hdx).m z).support :=
  (cycleCellCocycle R n x hx hdx).wellFounded_mem_support
    (fun _ _ ↦ cycleCellCocycle_m_eq_zero_of_le hx hdx) (p₀ := 0)
    (by rintro (_ | _) <;> simp; omega)

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
  simp [rowFiniteTwistedDifferential_single_koszulTwist, Finsupp.single_add]
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

/-- The generator `e₀` is a cycle. -/
theorem cycleCellCocycle_differential_single_inl_one :
    rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) (cycleCellCocycle R n x hx hdx).m
        (Finsupp.single (Sum.inl ()) 1) = 0 := by
  rw [RowFiniteTwistingCocycle.differential_single_one _ (loopChain_isDGAlgebra B b R),
    cycleCellCocycle_m_inl]

end CycleCell

/-! ### The augmentation -/

section Augmentation

variable {B : Type*} [TopologicalSpace B] {b : B} {R : Type*} [CommRing R]

variable (B b R) in
/-- The augmentation of the free module on the generators `Unit ⊕ Unit` of a cell cocycle such as
`TauCeti.cycleCellCocycle R n x`: the augmentation of the coefficient of the generator
`e₀ = Sum.inl ()` of index zero. -/
def loopCellAugmentation : (Unit ⊕ Unit →₀ loopChainAlgebra B b R) →ₗ[R] R :=
  (loopChainAugmentation B b R).toAlgHom.toLinearMap ∘ₗ Finsupp.lapply (Sum.inl ())

theorem loopCellAugmentation_apply (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    loopCellAugmentation B b R u = loopChainAugmentation B b R (u (Sum.inl ())) :=
  (rfl)

/-- The augmentation is linear over the augmentation of the loop chain algebra. -/
theorem loopCellAugmentation_smul (a : loopChainAlgebra B b R)
    (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    loopCellAugmentation B b R (a • u) =
      loopChainAugmentation B b R a * loopCellAugmentation B b R u := by
  simp [loopCellAugmentation_apply]

/-- The augmentation takes the augmentation of a coefficient of `e₀`; in particular it takes the
value `1` on the cycle `e₀`. -/
@[simp]
theorem loopCellAugmentation_single_inl (a : loopChainAlgebra B b R) :
    loopCellAugmentation B b R (Finsupp.single (Sum.inl ()) a) = loopChainAugmentation B b R a := by
  simp [loopCellAugmentation_apply]

/-- The augmentation vanishes on the multiples of `e₁`. -/
@[simp]
theorem loopCellAugmentation_single_inr (a : loopChainAlgebra B b R) :
    loopCellAugmentation B b R (Finsupp.single (Sum.inr ()) a) = 0 := by
  simp [loopCellAugmentation_apply]

variable (B b R) in
/-- The augmentation is surjective: it takes `r e₀` to `r`. -/
theorem loopCellAugmentation_surjective : Function.Surjective (loopCellAugmentation B b R) :=
  fun r ↦ ⟨Finsupp.single (Sum.inl ()) (algebraMap R _ r), by simp⟩

/-- When the attaching cycle has augmentation zero, as it does in positive dimension, the
augmentation of the free module of `TauCeti.cycleCellCocycle R n x` vanishes on boundaries. -/
@[simp]
theorem loopCellAugmentation_cycleCellCocycle_differential {n : ℕ} {x : loopChainAlgebra B b R}
    (hx : x ∈ cubicalChainGrading (MooreLoopSpace B b) R (-(n : ℤ)))
    (hdx : cubicalChainDifferential (MooreLoopSpace B b) R x = 0)
    (hεx : loopChainAugmentation B b R x = 0) (u : Unit ⊕ Unit →₀ loopChainAlgebra B b R) :
    loopCellAugmentation B b R
        (rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R)
          (cycleCellCocycle R n x hx hdx).m u) = 0 := by
  simp [loopCellAugmentation_apply, hεx]

end Augmentation

/-! ### The resolution of a cell attached along a cycle -/

section CycleCellResolution

variable {B : Type*} [TopologicalSpace B] {b : B} {R : Type*} [CommRing R] {n : ℕ}
  {x : loopChainAlgebra B b R} (hx : x ∈ cubicalChainGrading (MooreLoopSpace B b) R (-(n : ℤ)))
  (hdx : cubicalChainDifferential (MooreLoopSpace B b) R x = 0)

/-- The Koszul twist `κ` anticommutes with the differential of the loop chain algebra. -/
private theorem cubicalChainDifferential_koszulTwist (a : loopChainAlgebra B b R) :
    cubicalChainDifferential (MooreLoopSpace B b) R
        ((InternalGrading.ofDecomposition
          (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist 1 a) =
      -(InternalGrading.ofDecomposition
        (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist 1
          (cubicalChainDifferential (MooreLoopSpace B b) R a) := by
  rw [(loopChain_isDGAlgebra B b R).toIsNonUnitalDGAlgebra.koszulTwist_one_map, neg_neg]

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
  refine ⟨Finsupp.single (Sum.inl ()) w + Finsupp.single (Sum.inr ())
    ((InternalGrading.ofDecomposition
      (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist 1 β), ?_⟩
  simp [cycleCellCocycle_differential_single_inr, InternalGrading.koszulTwist_koszulTwist,
    cubicalChainDifferential_koszulTwist, hβ, ← hα, add_comm]

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
  have hu0 := congrArg (· (Sum.inl ())) hu
  have hu1 := congrArg (· (Sum.inr ())) hu
  simp only [hD, cycleCellCocycle_differential_apply_inl, cycleCellCocycle_differential_apply_inr,
    Finsupp.coe_zero, Pi.zero_apply] at hu0 hu1
  -- The coefficient `β` of `e₁` is a cycle with `κ(β) x` a boundary, so `κ(β) = dγ`.
  obtain ⟨γ, hγ⟩ := hinj _ (-u (Sum.inl ()))
    (by rw [cubicalChainDifferential_koszulTwist, hu1, map_zero, neg_zero])
    (by rw [map_neg]; exact neg_eq_of_add_eq_zero_right hu0)
  -- Subtracting the boundary of `-κ(γ) e₁` leaves a cycle `w` supported on `e₀`.
  set w := u - D (Finsupp.single (Sum.inr ()) (-(InternalGrading.ofDecomposition
    (cubicalChainGrading (MooreLoopSpace B b) R)).koszulTwist 1 γ)) with hw
  have hw1 : w (Sum.inr ()) = 0 := by
    simp [hw, hD, cycleCellCocycle_differential_single_inr, cubicalChainDifferential_koszulTwist,
      hγ, InternalGrading.koszulTwist_koszulTwist]
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

end CycleCellResolution

/-! ### A twisting cocycle on two generators -/

section TwoGenerators

variable {B : Type*} [TopologicalSpace B] {b : B} {R : Type*} [CommRing R] {P : Type*}
  [Fintype P] {ind : P → ℤ}

/-- **A twisting cocycle on two generators is the cocycle of a cell.** Let `m` be a twisting
cocycle over the loop chains `C_*(Ω_b B; R)` on two generators `p` and `q` with `ind q < ind p`,
whose entry `x = m p q`, a cycle (`TauCeti.TwistingCocycle.d_m_eq_zero_of_forall_eq_or_eq`), is an
`n`-chain. Relabelling `q` as `e₀` and `p` as `e₁`, its twisted complex
`C_*(Ω_b B; R) ⊗ ⟨p, q⟩` is the free module of `TauCeti.cycleCellCocycle R n x`. So if every cycle
of augmentation zero of the latter is a boundary, then so is every cycle `u` of the twisted complex
of `m` whose coefficient of `q` has augmentation zero. The Barraud–Cornea cocycle of a Morse
function with two critical points, such as the height function of a sphere, is an example. -/
theorem exists_twistedDifferential_eq_of_cycleCellCocycle
    (m : TwistingCocycle (R := R) (A := loopChainAlgebra B b R)
      (cubicalChainGrading (MooreLoopSpace B b) R)
      (cubicalChainDifferential (MooreLoopSpace B b) R) P ind) {p q : P}
    (hP : ∀ z, z = p ∨ z = q) (hind : ind q < ind p) {n : ℕ}
    (hx : m.m p q ∈ cubicalChainGrading (MooreLoopSpace B b) R (-(n : ℤ)))
    (hres : ∀ u : Unit ⊕ Unit →₀ loopChainAlgebra B b R,
      rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R)
        (cycleCellCocycle R n (m.m p q) hx (m.d_m_eq_zero_of_forall_eq_or_eq hP)).m u = 0 →
      loopCellAugmentation B b R u = 0 →
      ∃ v, rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R)
        (cycleCellCocycle R n (m.m p q) hx (m.d_m_eq_zero_of_forall_eq_or_eq hP)).m v = u)
    {u : P → loopChainAlgebra B b R}
    (hu : twistedDifferential m.m (cubicalChainGrading (MooreLoopSpace B b) R)
      (cubicalChainDifferential (MooreLoopSpace B b) R) u = 0)
    (hε : loopChainAugmentation B b R (u q) = 0) :
    ∃ v, twistedDifferential m.m (cubicalChainGrading (MooreLoopSpace B b) R)
      (cubicalChainDifferential (MooreLoopSpace B b) R) v = u := by
  classical
  have hpq : p ≠ q := ne_of_apply_ne ind hind.ne'
  have hDp := m.twistedDifferential_apply_left_of_forall_eq_or_eq hP
    (cubicalChainDifferential (MooreLoopSpace B b) R) hind (ℳ := cubicalChainGrading _ R)
  have hDq (f : P → loopChainAlgebra B b R) := (m.twistedDifferential_apply_right_of_forall_eq_or_eq
    hP (cubicalChainDifferential (MooreLoopSpace B b) R) f
      (ℳ := cubicalChainGrading (MooreLoopSpace B b) R)).trans (by rw [op_smul_eq_mul])
  have hu0 := congrArg (· p) hu
  have hu1 := congrArg (· q) hu
  simp only [Pi.zero_apply, hDp, hDq] at hu0 hu1
  -- Relabelled, `u` is the cycle `u q ⊗ e₀ + u p ⊗ e₁` of augmentation zero.
  obtain ⟨v, hv⟩ := hres
    (Finsupp.single (Sum.inl ()) (u q) + Finsupp.single (Sum.inr ()) (u p))
    (by
      refine Finsupp.ext fun i ↦ ?_
      rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      · rwa [cycleCellCocycle_differential_apply_inl, Finsupp.add_apply, Finsupp.add_apply,
          Finsupp.single_eq_same, Finsupp.single_eq_same, Finsupp.single_eq_of_ne Sum.inl_ne_inr,
          Finsupp.single_eq_of_ne Sum.inr_ne_inl, add_zero, zero_add, Finsupp.coe_zero,
          Pi.zero_apply]
      · rwa [cycleCellCocycle_differential_apply_inr, Finsupp.add_apply, Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne Sum.inr_ne_inl, zero_add, Finsupp.coe_zero, Pi.zero_apply])
    (by rwa [loopCellAugmentation_apply, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne Sum.inl_ne_inr, add_zero])
  have hv0 := congrArg (· (Sum.inl ())) hv
  have hv1 := congrArg (· (Sum.inr ())) hv
  simp only [cycleCellCocycle_differential_apply_inl, cycleCellCocycle_differential_apply_inr,
    Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne Sum.inl_ne_inr,
    Finsupp.single_eq_of_ne Sum.inr_ne_inl, add_zero, zero_add] at hv0 hv1
  -- Relabelled back, a preimage of `u` is `v e₁ ⊗ p + v e₀ ⊗ q`.
  refine ⟨Pi.single p (v (Sum.inr ())) + Pi.single q (v (Sum.inl ())), funext fun y ↦ ?_⟩
  rcases hP y with rfl | rfl
  · simp only [hDp, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hpq, add_zero, hv1]
  · simp only [hDq, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hpq,
      Pi.single_eq_of_ne hpq.symm, add_zero, zero_add, hv0]

end TwoGenerators

end TauCeti
