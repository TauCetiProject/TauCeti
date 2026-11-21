/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Ray

/-!
# Character weights of toric divisors

An integer ray coefficient family `a` allows precisely the characters `u` with
`u(vρ) + a ρ ≥ 0`, where `vρ` is the primitive generator of the ray `ρ`. On a cone chart
only the rays in that cone contribute. These weight sets index the monomials in the
corresponding divisor section modules, independently of the coefficient ring.

When a character `m` takes the values `-a ρ` on the rays of a cone, the chart weight set
is the translate by `m` of the dual semigroup. On a regular cone such an `m` exists, and
the difference of two chart generators is invertible as a character on their overlap.

## References

* P. Scholze, *Perfectoid spaces*, §8, Definition/Proposition 8.4 and the proof of
  Proposition 8.7.
-/

public section

open scoped Pointwise

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- The primitive lattice vector pointing along a ray of a fan. -/
noncomputable def Ray.primitiveGenerator (ρ : Φ.Ray) : N :=
  Toric.primitiveGenerator Φ.lattice (Φ.isToricCone ρ.toCone.property)
    (ρ.toToricRay Φ ρ.toCone le_rfl)

/-- The vector selected for a fan ray is also the primitive generator when the ray is viewed
inside any containing cone. -/
@[simp]
theorem Ray.primitiveGenerator_toToricRay (ρ : Φ.Ray) (σ : Φ.cones) (h : ρ.toCone ≤ σ) :
    Toric.primitiveGenerator Φ.lattice (Φ.isToricCone σ.property) (ρ.toToricRay Φ σ h) =
      ρ.primitiveGenerator := by
  have hv : IsPrimitiveGenerator i (ρ.toToricRay Φ ρ.toCone le_rfl) ρ.primitiveGenerator :=
    isPrimitiveGenerator_primitiveGenerator _ _ _
  have hmem : i ρ.primitiveGenerator ∈ (ρ.toToricRay Φ ρ.toCone le_rfl).toPointedCone := hv.mem
  have hmem' : i ρ.primitiveGenerator ∈ (ρ.toToricRay Φ σ h).toPointedCone := by
    simpa only [Ray.toPointedCone_toToricRay] using hmem
  have hv' : IsPrimitiveGenerator i (ρ.toToricRay Φ σ h) ρ.primitiveGenerator :=
    isPrimitiveGenerator_iff.mpr ⟨hmem', hv.isPrimitive⟩
  exact (hv'.eq_primitiveGenerator Φ.lattice (Φ.isToricCone σ.property)).symm

/-- The ray coefficients of the divisor of a character. -/
noncomputable def characterDivisor (Φ : Fan i) : (N →+ ℤ) →+ (Φ.Ray →₀ ℤ) :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ Φ.Ray).symm.toAddEquiv.toAddMonoidHom.comp
    (AddMonoidHom.pi fun ρ ↦ AddMonoidHom.eval ρ.primitiveGenerator)

/-- The coefficient of the character divisor at a ray is the character evaluated at its
primitive generator. -/
@[simp]
theorem characterDivisor_apply (u : N →+ ℤ) (ρ : Φ.Ray) :
    Φ.characterDivisor u ρ = u ρ.primitiveGenerator := by
  simp [characterDivisor]

/-- The characters satisfying all the ray inequalities for the given divisor coefficients. -/
def divisorWeights (Φ : Fan i) (a : Φ.Ray →₀ ℤ) : Set (N →+ ℤ) :=
  {u | ∀ ρ : Φ.Ray, 0 ≤ u ρ.primitiveGenerator + a ρ}

/-- The chart weights impose just the divisor inequalities for rays contained in the cone. -/
def coneDivisorWeights (Φ : Fan i) (σ : Φ.cones) (a : Φ.Ray →₀ ℤ) : Set (N →+ ℤ) :=
  {u | ∀ ρ : Φ.Ray, ρ.toCone ≤ σ → 0 ≤ u ρ.primitiveGenerator + a ρ}

/-- A global divisor weight satisfies the inequalities at every ray. -/
@[simp]
theorem mem_divisorWeights_iff {a : Φ.Ray →₀ ℤ} {u : N →+ ℤ} :
    u ∈ Φ.divisorWeights a ↔ ∀ ρ : Φ.Ray, 0 ≤ u ρ.primitiveGenerator + a ρ :=
  (Iff.rfl)

/-- A chart divisor weight satisfies the inequalities at the rays below its cone. -/
@[simp]
theorem mem_coneDivisorWeights_iff {σ : Φ.cones} {a : Φ.Ray →₀ ℤ} {u : N →+ ℤ} :
    u ∈ Φ.coneDivisorWeights σ a ↔
      ∀ ρ : Φ.Ray, ρ.toCone ≤ σ → 0 ≤ u ρ.primitiveGenerator + a ρ :=
  (Iff.rfl)

/-- Global admissibility is exactly simultaneous admissibility on every cone chart. -/
theorem divisorWeights_eq_iInter (a : Φ.Ray →₀ ℤ) :
    Φ.divisorWeights a = ⋂ σ : Φ.cones, Φ.coneDivisorWeights σ a := by
  ext u
  simp only [Set.mem_iInter, mem_divisorWeights_iff, mem_coneDivisorWeights_iff]
  exact ⟨fun h _ ρ _ ↦ h ρ, fun h ρ ↦ h ρ.toCone ρ le_rfl⟩

/-- Restricting to a face only drops inequalities. -/
theorem coneDivisorWeights_antitone (a : Φ.Ray →₀ ℤ) :
    Antitone (fun σ : Φ.cones ↦ Φ.coneDivisorWeights σ a) := by
  intro σ τ h u hu
  exact mem_coneDivisorWeights_iff.mpr fun ρ hρ ↦ mem_coneDivisorWeights_iff.mp hu ρ (hρ.trans h)

/-- On each chart, addition of weights is compatible with addition of divisor coefficients. -/
theorem add_mem_coneDivisorWeights {σ : Φ.cones} {a b : Φ.Ray →₀ ℤ} {u w : N →+ ℤ}
    (hu : u ∈ Φ.coneDivisorWeights σ a) (hw : w ∈ Φ.coneDivisorWeights σ b) :
    u + w ∈ Φ.coneDivisorWeights σ (a + b) := by
  simp only [mem_coneDivisorWeights_iff, AddMonoidHom.add_apply, Finsupp.add_apply] at *
  intro ρ hρ
  linarith [hu ρ hρ, hw ρ hρ]

/-- The sum of two global weights is a global weight for the sum of the divisors. -/
theorem add_mem_divisorWeights {a b : Φ.Ray →₀ ℤ} {u w : N →+ ℤ}
    (hu : u ∈ Φ.divisorWeights a) (hw : w ∈ Φ.divisorWeights b) :
    u + w ∈ Φ.divisorWeights (a + b) := by
  simp only [divisorWeights_eq_iInter, Set.mem_iInter] at *
  exact fun σ ↦ add_mem_coneDivisorWeights (hu σ) (hw σ)

/-- Adding the divisor of `m` translates the global weight set by `-m`. -/
theorem divisorWeights_add_characterDivisor (a : Φ.Ray →₀ ℤ) (m : N →+ ℤ) :
    Φ.divisorWeights (a + Φ.characterDivisor m) = -m +ᵥ Φ.divisorWeights a := by
  ext u
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, mem_divisorWeights_iff,
    Finsupp.add_apply, characterDivisor_apply, AddMonoidHom.add_apply]
  exact forall_congr' fun ρ ↦ by omega

/-- The chart weights for the zero divisor are exactly the dual semigroup. -/
@[simp]
theorem coneDivisorWeights_zero (σ : Φ.cones) :
    Φ.coneDivisorWeights σ 0 = (dualSemigroup Φ.lattice σ.val : Set (N →+ ℤ)) := by
  ext u
  rw [mem_coneDivisorWeights_iff, SetLike.mem_coe,
    mem_dualSemigroup_iff_primitiveGenerator Φ.lattice (Φ.isToricCone σ.property)]
  simp only [Finsupp.zero_apply, add_zero]
  constructor
  · intro h ρ
    let r := (Φ.rayEquiv σ).symm ρ
    have hr : r.val.toToricRay Φ σ r.property = ρ := by
      rw [← rayEquiv_apply, Equiv.apply_symm_apply]
    rw [← hr, Ray.primitiveGenerator_toToricRay]
    exact h r.val r.property
  · intro h ρ hρ
    simpa only [Ray.primitiveGenerator_toToricRay] using h (ρ.toToricRay Φ σ hρ)

/-- Adding a dual-semigroup character to a chart weight preserves its divisor inequalities. -/
theorem add_mem_coneDivisorWeights_of_mem_dualSemigroup {σ : Φ.cones} {a : Φ.Ray →₀ ℤ}
    {u p : N →+ ℤ} (hu : u ∈ Φ.coneDivisorWeights σ a) (hp : p ∈ dualSemigroup Φ.lattice σ.val) :
    u + p ∈ Φ.coneDivisorWeights σ a := by
  rw [← SetLike.mem_coe, ← coneDivisorWeights_zero] at hp
  simpa only [add_zero] using add_mem_coneDivisorWeights hu hp

/-- A chart character with value `-a ρ` on each ray gives a translation of the dual semigroup
onto the chart weights. -/
theorem coneDivisorWeights_eq_vadd (σ : Φ.cones) (a : Φ.Ray →₀ ℤ) (m : N →+ ℤ)
    (hm : ∀ ρ : Φ.Ray, ρ.toCone ≤ σ → m ρ.primitiveGenerator = -a ρ) :
    Φ.coneDivisorWeights σ a = m +ᵥ (dualSemigroup Φ.lattice σ.val : Set (N →+ ℤ)) := by
  rw [← coneDivisorWeights_zero]
  ext u
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, mem_coneDivisorWeights_iff,
    Finsupp.zero_apply, add_zero, AddMonoidHom.add_apply, AddMonoidHom.neg_apply]
  exact forall_congr' fun ρ ↦ imp_congr_right fun hρ ↦ by rw [hm ρ hρ, neg_neg, add_comm]

/-- Every integral ray coefficient family has a local Cartier character on a regular cone. -/
theorem exists_cartierCharacter (σ : Φ.cones) (hσ : IsRegularCone i σ.val) (a : Φ.Ray →₀ ℤ) :
    ∃ m : N →+ ℤ, ∀ ρ : Φ.Ray, ρ.toCone ≤ σ → m ρ.primitiveGenerator = -a ρ := by
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  let f : ToricRay σ.val ⊕ Fin l → ℤ := Sum.elim (fun ρ ↦ -a (Ray.ofToricRay Φ σ ρ)) 0
  refine ⟨(b.constr ℤ f).toAddMonoidHom, fun ρ hρ ↦ ?_⟩
  let r := ρ.toToricRay Φ σ hρ
  have hr : Ray.ofToricRay Φ σ r = ρ := by
    simpa only [rayEquiv_apply, rayEquiv_symm_apply, Subtype.coe_mk, r] using
      congrArg Subtype.val ((Φ.rayEquiv σ).symm_apply_apply ⟨ρ, hρ⟩)
  have hv : b (Sum.inl r) = ρ.primitiveGenerator := by
    rw [(hb r).eq_primitiveGenerator Φ.lattice (Φ.isToricCone σ.property)]
    exact ρ.primitiveGenerator_toToricRay σ hρ
  rw [← hv]
  simp [f, hr]

/-- Local Cartier characters for the same coefficients have a difference lying in the dual
semigroup of the overlap. Applying this in the reverse order gives its inverse there. -/
theorem sub_mem_dualSemigroup_inf {σ τ : Φ.cones} {a : Φ.Ray →₀ ℤ} {m n : N →+ ℤ}
    (hm : ∀ ρ : Φ.Ray, ρ.toCone ≤ σ → m ρ.primitiveGenerator = -a ρ)
    (hn : ∀ ρ : Φ.Ray, ρ.toCone ≤ τ → n ρ.primitiveGenerator = -a ρ) :
    m - n ∈ dualSemigroup Φ.lattice (σ ⊓ τ).val := by
  rw [← SetLike.mem_coe, ← coneDivisorWeights_zero, mem_coneDivisorWeights_iff]
  intro ρ hρ
  simp [hm ρ (hρ.trans inf_le_left), hn ρ (hρ.trans inf_le_right)]

end TauCeti.Toric.Fan
