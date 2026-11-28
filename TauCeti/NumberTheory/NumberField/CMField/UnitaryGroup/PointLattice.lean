/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdelicFrame
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Lattices of finite adelic points

For a hermitian space with adelic frame `V = (J, x)` and a finite unitary point `g`,
`V.finiteLattice g` is the integral adelic module `(x_f g) Ôⁿ`, in rational coordinates.
The form `V.finiteForm y z = y* J z` makes this module self-dual: integrality of the
pairings with its vectors characterizes membership. Moreover, inclusion of two such modules
is equivalent to equality, and to membership of the relative point in the standard integral
unitary subgroup. Thus the lattices are indexed exactly by the left cosets `g K₀` of the
standard integral unitary subgroup. Each lattice is compact, and a rational isometry
`γ ∈ U(J)(E⁺)` carries the lattice of `g` onto the lattice of `x_f⁻¹ γ x_f g`, the point moved by
the finite component of the rational embedding of `γ`.

These are modules over the integral finite adeles, rather than the modules of rational
integral vectors `V.lattice`. The latter are recovered by intersecting with the rational
vectors. No condition on roots of unity, grading, or unramifiedness is needed here.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §82, for self-dual lattices.

The statements correspond to `New.Space.mem_lattice_iff_formFin`, `New.Space.lattice_le_iff`
and `New.Space.lattice_eq_iff` in `src/Lib/Weil/Periods/PointLattice.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0). The proofs here use the existing adelic
frame and integral subgroup APIs; no code from that project is copied.
-/

public noncomputable section

open IsDedekindDomain Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti.FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → ℤˣ}
  (V : FramedHermitianSpace E s)

/-- The integral adelic module `(x_f g) Ôⁿ` of a finite unitary point, in rational coordinates. -/
def finiteLattice (g : finiteAdelicUnitaryGroup E ι) :
    Submodule (FiniteAdeleRing.integralAdeles (𝓞 E) E) (ι → 𝔸ᶠ[E]) :=
  (Submodule.pi Set.univ fun _ : ι ↦
    (1 : Submodule (FiniteAdeleRing.integralAdeles (𝓞 E) E) 𝔸ᶠ[E])).comap
      (((↑(V.frame.2 * g)⁻¹ : Matrix ι ι 𝔸ᶠ[E]).mulVecLin).restrictScalars _)

/-- Membership is integrality of every coordinate in the moved frame. -/
@[simp]
theorem mem_finiteLattice_iff (g : finiteAdelicUnitaryGroup E ι) (z : ι → 𝔸ᶠ[E]) :
    z ∈ V.finiteLattice g ↔ ∀ i,
      ((↑(V.frame.2 * g)⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ z) i ∈
        FiniteAdeleRing.integralAdeles (𝓞 E) E := by
  simp [finiteLattice, Submodule.mem_pi, Submodule.mem_one, Subalgebra.algebraMap_eq]

/-- The finite hermitian pairing `y* J z` in rational coordinates: the sesquilinear form of the
Gram matrix, conjugate-linear in the first vector. -/
def finiteForm : (ι → 𝔸ᶠ[E]) →ₗ⋆[𝔸ᶠ[E]] (ι → 𝔸ᶠ[E]) →ₗ[𝔸ᶠ[E]] 𝔸ᶠ[E] :=
  Matrix.toLinearMapₛₗ₂' 𝔸ᶠ[E] (starRingEnd 𝔸ᶠ[E]) (RingHom.id 𝔸ᶠ[E])
    (V.gram.map (algebraMap E 𝔸ᶠ[E]))

/-- The defining formula for the finite pairing. -/
theorem finiteForm_def (y z : ι → 𝔸ᶠ[E]) :
    V.finiteForm y z = star y ⬝ᵥ (V.gram.map (algebraMap E 𝔸ᶠ[E]) *ᵥ z) := by
  simp only [finiteForm, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, mulVec, Finset.mul_sum,
    starRingEnd_apply, RingHom.id_apply, smul_eq_mul, Pi.star_apply]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Swapping the vectors conjugates the finite pairing. -/
@[simp]
theorem star_finiteForm (y z : ι → 𝔸ᶠ[E]) :
    star (V.finiteForm y z) = V.finiteForm z y := by
  rw [finiteForm_def, finiteForm_def]
  exact (V.isHermitian_gram.map (algebraMap E 𝔸ᶠ[E])
    (fun a ↦ algebraMap_star_comm a)).star_dotProduct_mulVec_comm y z

/-- Coordinates in the moved finite frame invert the moved frame. -/
private theorem inv_mulVec_frame_mulVec (g : finiteAdelicUnitaryGroup E ι) (y : ι → 𝔸ᶠ[E]) :
    (↑(V.frame.2 * g)⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ ((↑(V.frame.2 * g) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ y) =
      y := by
  rw [mulVec_mulVec, Units.inv_mul, one_mulVec]

/-- The moved finite frame inverts its coordinates. -/
private theorem frame_mulVec_inv_mulVec (g : finiteAdelicUnitaryGroup E ι) (y : ι → 𝔸ᶠ[E]) :
    (↑(V.frame.2 * g) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ ((↑(V.frame.2 * g)⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ y) =
      y := by
  rw [mulVec_mulVec, Units.mul_inv, one_mulVec]

/-- In the moved finite frame the pairing is the standard hermitian dot product. -/
theorem finiteForm_mulVec (g : finiteAdelicUnitaryGroup E ι) (y z : ι → 𝔸ᶠ[E]) :
    V.finiteForm ((↑(V.frame.2 * g) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ y)
      ((↑(V.frame.2 * g) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ z) = star y ⬝ᵥ z := by
  have hframe : (↑(V.frame.2 * g) : Matrix ι ι 𝔸ᶠ[E])ᴴ *
      V.gram.map (algebraMap E 𝔸ᶠ[E]) * (↑(V.frame.2 * g) : Matrix ι ι 𝔸ᶠ[E]) = 1 :=
    star_mul_mul_mul_eq_of_mem_unitaryGroupOf V.star_mul_gram_mul_snd
      (unitaryGroupOf_one.ge g.property)
  rw [finiteForm_def, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, hframe, one_mulVec]

/-- Pairings may be computed from the coordinates of both vectors in any moved finite frame. -/
theorem finiteForm_eq_dotProduct (g : finiteAdelicUnitaryGroup E ι) (y z : ι → 𝔸ᶠ[E]) :
    V.finiteForm y z =
      star ((↑(V.frame.2 * g)⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ y) ⬝ᵥ
        ((↑(V.frame.2 * g)⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ z) := by
  rw [← V.finiteForm_mulVec g, V.frame_mulVec_inv_mulVec, V.frame_mulVec_inv_mulVec]

/-- Multiplication by the moved finite frame identifies integral vectors with its lattice. -/
theorem mulVec_mem_finiteLattice_iff (g : finiteAdelicUnitaryGroup E ι) (y : ι → 𝔸ᶠ[E]) :
    (↑(V.frame.2 * g) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ y ∈ V.finiteLattice g ↔
      ∀ i, y i ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E := by
  rw [V.mem_finiteLattice_iff, V.inv_mulVec_frame_mulVec]

/-- Each column `x_f g eᵢ` of the moved frame is a vector of its finite lattice. -/
theorem mulVec_single_one_mem_finiteLattice (g : finiteAdelicUnitaryGroup E ι) (i : ι) :
    (↑(V.frame.2 * g) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ Pi.single i 1 ∈ V.finiteLattice g := by
  rw [V.mulVec_mem_finiteLattice_iff]
  intro j
  by_cases hij : i = j <;> simp [hij]

/-- Pairings of two vectors of the same finite lattice are integral. -/
theorem finiteForm_mem_integralAdeles (g : finiteAdelicUnitaryGroup E ι)
    {y z : ι → 𝔸ᶠ[E]} (hy : y ∈ V.finiteLattice g) (hz : z ∈ V.finiteLattice g) :
    V.finiteForm y z ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E := by
  rw [V.finiteForm_eq_dotProduct g]
  exact Subalgebra.sum_mem _ fun i _ ↦ Subalgebra.mul_mem _
    (star_mem_integralAdeles_iff.2 ((V.mem_finiteLattice_iff g y).1 hy i))
    ((V.mem_finiteLattice_iff g z).1 hz i)

/-- Self-duality: integral pairings against the lattice characterize its vectors. -/
theorem mem_finiteLattice_iff_finiteForm (g : finiteAdelicUnitaryGroup E ι) (z : ι → 𝔸ᶠ[E]) :
    z ∈ V.finiteLattice g ↔ ∀ y ∈ V.finiteLattice g,
      V.finiteForm y z ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E := by
  refine ⟨fun hz y hy ↦ V.finiteForm_mem_integralAdeles g hy hz, fun h ↦ ?_⟩
  rw [V.mem_finiteLattice_iff]
  intro i
  have h' := h _ (V.mulVec_single_one_mem_finiteLattice g i)
  rw [V.finiteForm_eq_dotProduct g, V.inv_mulVec_frame_mulVec] at h'
  simpa only [Pi.star_single, star_one, single_dotProduct, one_mul] using h'

/-- Inclusion of point lattices is membership of the relative point in the integral subgroup. -/
theorem finiteLattice_le_iff (g h : finiteAdelicUnitaryGroup E ι) :
    V.finiteLattice h ≤ V.finiteLattice g ↔
      g⁻¹ * h ∈ integralAdelicUnitaryGroup E ι := by
  have hcoords (y : ι → 𝔸ᶠ[E]) :
      (↑(V.frame.2 * g)⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ
        ((↑(V.frame.2 * h) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ y) =
          (↑((g⁻¹ * h : finiteAdelicUnitaryGroup E ι) : GL ι 𝔸ᶠ[E]) :
            Matrix ι ι 𝔸ᶠ[E]) *ᵥ y := by
    simp only [mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev,
      mul_assoc, inv_mul_cancel_left, Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨fun hle ↦ mem_integralAdelicUnitaryGroup_iff.2 fun i j ↦ ?_, fun hint y hy ↦ ?_⟩
  · have := (V.mem_finiteLattice_iff g _).1 (hle (V.mulVec_single_one_mem_finiteLattice h j)) i
    rwa [hcoords, mulVec_single_one] at this
  · rw [V.mem_finiteLattice_iff] at hy ⊢
    rw [← V.frame_mulVec_inv_mulVec h y, hcoords]
    exact (FiniteAdeleRing.forall_mulVec_mem_integralAdeles_iff
      (mem_integralAdelicUnitaryGroup_iff_mem_range_integralGL.1 hint)).2 hy

/-- Two self-dual point lattices cannot be strictly included in one another. -/
theorem finiteLattice_eq_of_le {g h : finiteAdelicUnitaryGroup E ι}
    (hgh : V.finiteLattice h ≤ V.finiteLattice g) : V.finiteLattice h = V.finiteLattice g := by
  apply le_antisymm hgh
  rw [V.finiteLattice_le_iff] at hgh ⊢
  simpa using (integralAdelicUnitaryGroup E ι).inv_mem hgh

/-- Equality of lattices is equality of the left cosets `g K₀ = h K₀` of the standard integral
subgroup. -/
theorem finiteLattice_eq_iff (g h : finiteAdelicUnitaryGroup E ι) :
    V.finiteLattice g = V.finiteLattice h ↔ g⁻¹ * h ∈ integralAdelicUnitaryGroup E ι := by
  rw [← V.finiteLattice_le_iff]
  exact ⟨fun h ↦ h.ge, fun h ↦ (V.finiteLattice_eq_of_le h).symm⟩

/-- Right multiplication by an integral unitary point leaves the lattice unchanged. -/
theorem finiteLattice_mul_of_mem_integralAdelicUnitaryGroup (g k : finiteAdelicUnitaryGroup E ι)
    (hk : k ∈ integralAdelicUnitaryGroup E ι) : V.finiteLattice (g * k) = V.finiteLattice g := by
  symm
  simpa [V.finiteLattice_eq_iff] using hk

/-- Rational points in the finite lattice at the identity are the integral rational lattice. -/
theorem mem_finiteLattice_one_iff (y : ι → E) :
    (algebraMap E 𝔸ᶠ[E] ∘ y) ∈ V.finiteLattice 1 ↔ y ∈ V.lattice := by
  simp only [mem_finiteLattice_iff, mem_lattice_iff, OneMemClass.coe_one, mul_one]

/-- **The point lattices are compact**: the lattice of `g` is the image of the compact set `Ôⁿ`
under the moved frame `x_f g`. -/
theorem isCompact_finiteLattice (g : finiteAdelicUnitaryGroup E ι) :
    IsCompact (V.finiteLattice g : Set (ι → 𝔸ᶠ[E])) := by
  have hO : IsCompact (Set.univ.pi fun _ : ι ↦
      (FiniteAdeleRing.integralAdeles (𝓞 E) E : Set 𝔸ᶠ[E])) :=
    isCompact_univ_pi fun _ ↦ FiniteAdeleRing.isCompact_integralAdeles
  have himage : (V.finiteLattice g : Set (ι → 𝔸ᶠ[E])) =
      (fun v ↦ (↑(V.frame.2 * g) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ v) '' Set.univ.pi fun _ ↦
        (FiniteAdeleRing.integralAdeles (𝓞 E) E : Set 𝔸ᶠ[E]) := by
    ext z
    refine ⟨fun hz ↦ ⟨_, fun i _ ↦ (V.mem_finiteLattice_iff g z).1 hz i,
      V.frame_mulVec_inv_mulVec g z⟩, ?_⟩
    rintro ⟨v, hv, rfl⟩
    exact (V.mulVec_mem_finiteLattice_iff g v).2 fun i ↦ hv i (Set.mem_univ i)
  rw [himage]
  exact hO.image (continuous_const.matrix_mulVec continuous_id)

/-- **Rational isometries move the point lattices.** For `γ ∈ U(J)(E⁺)`, read diagonally over
`𝔸_f`, multiplication by `γ` carries the lattice of `g` onto the lattice of `x_f⁻¹ γ x_f g`, the
product of the finite component of the rational embedding of `γ` with `g`. -/
theorem mulVec_mem_finiteLattice_rationalEmbedding_mul_iff (γ : unitaryGroupOf V.gram)
    (g : finiteAdelicUnitaryGroup E ι) (z : ι → 𝔸ᶠ[E]) :
    (↑(GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) (γ : GL ι E)) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ z ∈
        V.finiteLattice (adelicUnitaryGroup.finitePart E s (V.rationalEmbedding γ) * g) ↔
      z ∈ V.finiteLattice g := by
  -- The moved frame is `x_f (x_f⁻¹ γ x_f g) = γ (x_f g)`.
  have hframe : V.frame.2 * ((adelicUnitaryGroup.finitePart E s (V.rationalEmbedding γ) * g :
      finiteAdelicUnitaryGroup E ι) : GL ι 𝔸ᶠ[E]) =
        GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) (γ : GL ι E) * (V.frame.2 * g) := by
    simp only [Subgroup.coe_mul, adelicUnitaryGroup.coe_finitePart, coe_rationalEmbedding,
      ← mul_assoc, mul_inv_cancel, one_mul]
  have hγ : (↑(GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) (γ : GL ι E))⁻¹ :
      Matrix ι ι 𝔸ᶠ[E]) *ᵥ ((↑(GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) (γ : GL ι E)) :
        Matrix ι ι 𝔸ᶠ[E]) *ᵥ z) = z := by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  rw [V.mem_finiteLattice_iff, V.mem_finiteLattice_iff, hframe, _root_.mul_inv_rev,
    Units.val_mul, ← mulVec_mulVec, hγ]

end TauCeti.FramedHermitianSpace
