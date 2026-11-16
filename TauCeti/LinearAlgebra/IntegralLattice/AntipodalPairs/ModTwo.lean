/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Int
public import TauCeti.LinearAlgebra.IntegralLattice.AntipodalPairs.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
public import TauCeti.RingTheory.QuotSMulTop

/-!
# Minimal-vector pairs modulo twice a lattice

Two vectors of minimum positive norm in a positive definite integral lattice have the same
residue modulo `2L` exactly when they differ by sign. Indeed, if `x - y = 2z`, then `z` and `y + z`
belong to the lattice and their norms sum to the minimum. They cannot both be nonzero.
Thus antipodal pairs of minimal vectors identify with the residue classes represented by
minimal vectors. This identification intertwines lattice isometries and reduction modulo two.

The sign-independent map exists on every norm shell; it is injective whenever the shell
norm is less than twice every nonzero lattice norm. No unimodularity or enumeration of
the lattice is needed.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 10.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- The residue classes modulo `2L` represented by vectors of norm `n`. -/
def normClassesModTwo (n : ℚ) : Set (QuotSMulTop (2 : ℤ) L) :=
  Submodule.Quotient.mk '' L.vectorsOfNorm n

/-- The norm-class set is the image of the norm shell under reduction modulo two. -/
theorem normClassesModTwo_def (n : ℚ) :
    L.normClassesModTwo n = Submodule.Quotient.mk '' L.vectorsOfNorm n := (rfl)

/-- A residue class lies in the norm shell image exactly when it has a representative there. -/
theorem mem_normClassesModTwo {n : ℚ} {c : QuotSMulTop (2 : ℤ) L} :
    c ∈ L.normClassesModTwo n ↔
      ∃ x ∈ L.vectorsOfNorm n, Submodule.Quotient.mk x = c := Iff.rfl

/-- A vector on the norm shell represents a class in its mod-two image. -/
theorem mk_mem_normClassesModTwo {n : ℚ} {x : L} (hx : x ∈ L.vectorsOfNorm n) :
    (Submodule.Quotient.mk x : QuotSMulTop (2 : ℤ) L) ∈ L.normClassesModTwo n :=
  L.mem_normClassesModTwo.mpr ⟨x, hx, rfl⟩

/-- The classes represented on any norm shell form a finite type. -/
instance instFiniteNormClassesModTwo (n : ℚ) : Finite (L.normClassesModTwo n) := by
  have : Finite (QuotSMulTop (2 : ℤ) L) := finite_quotSMulTop_int 2 L
  infer_instance

/-- Every norm shell has finitely many represented mod-two classes. -/
theorem finite_normClassesModTwo (n : ℚ) : (L.normClassesModTwo n).Finite :=
  Set.toFinite _

/-- Reduction of an isometry preserves membership in every represented norm shell. -/
@[simp]
theorem Isometry.reductionHom_mem_normClassesModTwo_iff (g : Isometry L L) (n : ℚ)
    (c : QuotSMulTop (2 : ℤ) L) :
    Isometry.reductionHom L 2 g c ∈ L.normClassesModTwo n ↔ c ∈ L.normClassesModTwo n := by
  induction c using Submodule.Quotient.induction_on with
  | _ x =>
    rw [Isometry.reductionHom_apply_mk]
    constructor
    · intro hc
      obtain ⟨y, hy, h⟩ := L.mem_normClassesModTwo.mp hc
      refine L.mem_normClassesModTwo.mpr ⟨g.carrierEquiv.symm y, ?_, ?_⟩
      · exact (g.carrierEquiv_mem_vectorsOfNorm_iff _ n).mp (by simpa using hy)
      · have h' := congrArg (Isometry.reductionHom L 2 g.symm) h
        simpa only [Isometry.reductionHom_apply_mk, Isometry.carrierEquiv_symm,
          LinearEquiv.symm_apply_apply] using h'
    · intro hc
      obtain ⟨y, hy, h⟩ := L.mem_normClassesModTwo.mp hc
      refine L.mem_normClassesModTwo.mpr ⟨g.carrierEquiv y,
        (g.carrierEquiv_mem_vectorsOfNorm_iff y n).mpr hy, ?_⟩
      simpa only [Isometry.reductionHom_apply_mk] using
        congrArg (Isometry.reductionHom L 2 g) h

/-- Vectors whose combined norm is below four times every nonzero lattice norm are
congruent modulo `2L` exactly when they differ by sign. -/
theorem quotSMulTop_two_mk_eq_iff {x y : L}
    (hmin : ∀ z : L, z ≠ 0 → L.norm x + L.norm y < 4 * L.norm z) :
    (Submodule.Quotient.mk x : QuotSMulTop (2 : ℤ) L) = Submodule.Quotient.mk y ↔
      x = y ∨ x = -y := by
  constructor
  · intro h
    obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists
      (x - y) (2 : ℤ) (⊤ : Submodule ℤ L)).mp ((Submodule.Quotient.eq _).mp h)
    have hx' : x = y + (2 : ℤ) • z := by rw [hz]; abel
    by_cases hz0 : z = 0
    · exact Or.inl (by simpa [hz0] using hx')
    by_cases hyz : y + z = 0
    · right
      have hz' : z = -y := eq_neg_of_add_eq_zero_right hyz
      simp [hx', hz', two_zsmul]
    have h₁ := hmin z hz0
    have h₂ := hmin (y + z) hyz
    -- Work on ambient vectors only to use the rational norm's polarization identities.
    have hxambient : (x : V) = (y : V) + ((z : V) + z) := by
      simpa only [two_zsmul, Submodule.coe_add] using congrArg Subtype.val hx'
    have hxnorm := congrArg L.norm hxambient
    rw [L.norm_add, L.norm_add, map_add, L.norm_apply (z : V)] at hxnorm
    rw [Submodule.coe_add, L.norm_add] at h₂
    linarith [L.norm_apply (z : V)]
  · rintro (rfl | rfl)
    · rfl
    · simp

/-- Send an antipodal pair to its common residue modulo `2L`. -/
noncomputable def antipodalPairsToModTwo (n : ℚ) (p : L.antipodalPairs n) :
    L.normClassesModTwo n :=
  ⟨Submodule.Quotient.mk (mem_antipodalPairs.mp p.property).choose,
    ⟨(mem_antipodalPairs.mp p.property).choose,
      (mem_antipodalPairs.mp p.property).choose_spec.1, rfl⟩⟩

/-- The residue of a pair is the residue of either of its vector representatives. -/
@[simp]
theorem coe_antipodalPairsToModTwo_mk {n : ℚ} (x : L)
    (hp : s(x, -x) ∈ L.antipodalPairs n) :
    (L.antipodalPairsToModTwo n ⟨s(x, -x), hp⟩ :
      QuotSMulTop (2 : ℤ) L) = Submodule.Quotient.mk x := by
  unfold antipodalPairsToModTwo
  have hpair := (mem_antipodalPairs.mp hp).choose_spec.2
  rcases Sym2.eq_iff.mp hpair with ⟨h, -⟩ | ⟨h, -⟩
  · exact congrArg Submodule.Quotient.mk h
  · exact (congrArg (fun z : L ↦
      (Submodule.Quotient.mk z : QuotSMulTop (2 : ℤ) L)) h).trans (by simp)

/-- Every residue class represented on the shell is the image of an antipodal pair. -/
theorem antipodalPairsToModTwo_surjective (n : ℚ) :
    Function.Surjective (L.antipodalPairsToModTwo n) := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx, rfl⟩ := L.mem_normClassesModTwo.mp hc
  exact ⟨⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩,
    Subtype.ext (L.coe_antipodalPairsToModTwo_mk x _)⟩

/-- Reduction modulo two separates antipodal pairs below twice every nonzero norm. -/
theorem antipodalPairsToModTwo_injective {n : ℚ}
    (hmin : ∀ z : L, z ≠ 0 → n < 2 * L.norm z) :
    Function.Injective (L.antipodalPairsToModTwo n) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ h
  obtain ⟨x, hx, rfl⟩ := mem_antipodalPairs.mp hp
  obtain ⟨y, hy, rfl⟩ := mem_antipodalPairs.mp hq
  have hxy := congrArg Subtype.val h
  simp only [L.coe_antipodalPairsToModTwo_mk] at hxy
  have hbound (z : L) (hz : z ≠ 0) : L.norm x + L.norm y < 4 * L.norm z := by
    rw [mem_vectorsOfNorm.mp hx, mem_vectorsOfNorm.mp hy]
    linarith [hmin z hz]
  rcases (L.quotSMulTop_two_mk_eq_iff hbound).mp hxy with rfl | rfl <;>
    apply Subtype.ext <;> simp [Sym2.eq_swap]

/-- Antipodal pairs below twice every nonzero norm identify with their actual mod-two classes. -/
noncomputable def antipodalPairsEquivModTwo {n : ℚ}
    (hmin : ∀ z : L, z ≠ 0 → n < 2 * L.norm z) :
    L.antipodalPairs n ≃ L.normClassesModTwo n :=
  Equiv.ofBijective (L.antipodalPairsToModTwo n)
    ⟨L.antipodalPairsToModTwo_injective hmin, L.antipodalPairsToModTwo_surjective n⟩

/-- The equivalence sends a pair to the residue of either representative. -/
theorem antipodalPairsEquivModTwo_apply {n : ℚ}
    (hmin : ∀ z : L, z ≠ 0 → n < 2 * L.norm z) (p : L.antipodalPairs n) :
    L.antipodalPairsEquivModTwo hmin p = L.antipodalPairsToModTwo n p := (rfl)

/-- Evaluate the equivalence on an explicit antipodal pair. -/
@[simp]
theorem coe_antipodalPairsEquivModTwo_mk {n : ℚ}
    (hmin : ∀ z : L, z ≠ 0 → n < 2 * L.norm z) (x : L)
    (hp : s(x, -x) ∈ L.antipodalPairs n) :
    (L.antipodalPairsEquivModTwo hmin ⟨s(x, -x), hp⟩ : QuotSMulTop (2 : ℤ) L) =
      Submodule.Quotient.mk x := by
  rw [L.antipodalPairsEquivModTwo_apply, L.coe_antipodalPairsToModTwo_mk]

/-- The inverse equivalence recovers the sign pair of a representative on the shell. -/
@[simp]
theorem antipodalPairsEquivModTwo_symm_mk {n : ℚ}
    (hmin : ∀ z : L, z ≠ 0 → n < 2 * L.norm z) (x : L)
    (hx : x ∈ L.vectorsOfNorm n)
    (hc : (Submodule.Quotient.mk x : QuotSMulTop (2 : ℤ) L) ∈ L.normClassesModTwo n) :
    (L.antipodalPairsEquivModTwo hmin).symm ⟨Submodule.Quotient.mk x, hc⟩ =
      ⟨s(x, -x), (mk_mem_antipodalPairs_iff x).mpr hx⟩ := by
  apply (L.antipodalPairsEquivModTwo hmin).symm_apply_eq.mpr
  exact Subtype.ext (L.coe_antipodalPairsEquivModTwo_mk hmin x _).symm

/-- The pair-to-residue map intertwines the pair action with reduction of a lattice isometry. -/
theorem coe_antipodalPairsToModTwo_antipodalPairsEquiv (n : ℚ) (g : Isometry L L)
    (p : L.antipodalPairs n) :
    (L.antipodalPairsToModTwo n (g.antipodalPairsEquiv n p) : QuotSMulTop (2 : ℤ) L) =
      Isometry.reductionHom L 2 g (L.antipodalPairsToModTwo n p) := by
  rcases p with ⟨p, hp⟩
  obtain ⟨x, hx, rfl⟩ := mem_antipodalPairs.mp hp
  have hgx := (g.carrierEquiv_mem_vectorsOfNorm_iff x n).mpr hx
  have hpair : g.antipodalPairsEquiv n ⟨s(x, -x), hp⟩ =
      ⟨s(g.carrierEquiv x, -g.carrierEquiv x), (mk_mem_antipodalPairs_iff _).mpr hgx⟩ := by
    apply Subtype.ext
    simp
  rw [hpair, L.coe_antipodalPairsToModTwo_mk, L.coe_antipodalPairsToModTwo_mk,
    Isometry.reductionHom_apply_mk]

/-- The equivalence intertwines the pair action with reduction of a lattice isometry. -/
theorem coe_antipodalPairsEquivModTwo_antipodalPairsEquiv {n : ℚ}
    (hmin : ∀ z : L, z ≠ 0 → n < 2 * L.norm z) (g : Isometry L L)
    (p : L.antipodalPairs n) :
    (L.antipodalPairsEquivModTwo hmin (g.antipodalPairsEquiv n p) :
      QuotSMulTop (2 : ℤ) L) =
      Isometry.reductionHom L 2 g (L.antipodalPairsEquivModTwo hmin p) := by
  simpa only [L.antipodalPairsEquivModTwo_apply] using
    L.coe_antipodalPairsToModTwo_antipodalPairsEquiv n g p

/-- An isometry carries one pair to another exactly when its reduction carries their classes. -/
theorem antipodalPairsEquiv_eq_iff {n : ℚ}
    (hmin : ∀ z : L, z ≠ 0 → n < 2 * L.norm z) (g : Isometry L L)
    (p q : L.antipodalPairs n) :
    g.antipodalPairsEquiv n p = q ↔
      Isometry.reductionHom L 2 g (L.antipodalPairsToModTwo n p) =
        (L.antipodalPairsToModTwo n q : QuotSMulTop (2 : ℤ) L) := by
  rw [← (L.antipodalPairsToModTwo_injective hmin).eq_iff, Subtype.ext_iff,
    L.coe_antipodalPairsToModTwo_antipodalPairsEquiv]

end TauCeti.IntegralLattice
