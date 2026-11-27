/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Ray
public import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

/-!
# Character weights of invariant divisors

An invariant divisor `D = ∑ a_ρ D_ρ` on the toric variety of a fan is recorded by its integer
coefficients `a : Phi.Ray → ℤ`, one for each ray. Its *character weights* are the integral
characters `u : N →+ ℤ` with `u v_ρ ≥ -a_ρ` for the primitive generator `v_ρ` of every ray `ρ`.
The global sections of `O(D)` are spanned by the characters `χ ^ u` with `u` a weight
(Cox–Little–Schenck, Proposition 4.3.3), so the weights index the monomial basis of the module of
sections. For a single cone `σ` of the fan only the inequalities for the rays of `σ` are imposed;
these local weights index the monomial sections of `O(D)` over the affine chart of `σ`.

The global weights are the intersection of the local ones. The local weights of `σ` are stable
under adding characters of the dual semigroup `P_σ` of `σ`, which is the module structure of the
sections over the affine chart. The weights of `0` on `σ` are exactly `P_σ`. If a character
`m_σ` satisfies the Cartier equations `m_σ v_ρ = -a_ρ` on the rays of `σ`, the local weights are
the translate `m_σ + P_σ`, and on a regular cone such a character always exists. Adding the
divisor of a character `χ ^ m`, whose coefficient at `ρ` is `m v_ρ`, translates the weights by
`-m`, and weights of two divisors add to weights of their sum.

No effectivity or ampleness is assumed: the weights need not contain `0` (this happens exactly
when `D` is effective), and they need not be closed under addition.

## Main declarations

* `TauCeti.Toric.Fan.characterDivisor`: the coefficients `u v_ρ` of the divisor of a character.
* `TauCeti.Toric.Fan.divisorWeights`: the character weights of an invariant divisor.
* `TauCeti.Toric.Fan.coneDivisorWeights`: the character weights on a single cone.
* `TauCeti.Toric.Fan.divisorWeights_add_characterDivisor`: adding the divisor of `χ ^ m`
  translates the weights by `-m`.
* `TauCeti.Toric.Fan.divisorWeights_add_subset`: weights of two divisors add to weights of their
  sum.
* `TauCeti.Toric.Fan.iInter_coneDivisorWeights`: the global weights are the intersection of the
  local ones.
* `TauCeti.Toric.Fan.add_mem_coneDivisorWeights`: the local weights are stable under the dual
  semigroup.
* `TauCeti.Toric.Fan.coneDivisorWeights_eq_vadd`: Cartier data `m_σ` identify the local weights
  with `m_σ + P_σ`, and `TauCeti.Toric.Fan.exists_coneDivisorWeights_eq_vadd` provides it on a
  regular cone.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §8, Definition/Proposition 8.4
  and the proof of Proposition 8.7.
* W. Fulton, *Introduction to Toric Varieties*, §§3.3 and 3.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §4.2 and Proposition 4.3.3.
-/

public section

open scoped Pointwise

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Phi : Fan i)

/-! ### The divisor of a character -/

/-- The coefficients of the divisor of the character `χ ^ u` along the invariant divisors: the
coefficient at a ray is the value of `u` on its primitive generator. -/
noncomputable def characterDivisor : (N →+ ℤ) →+ (Phi.Ray → ℤ) :=
  AddMonoidHom.pi fun rho ↦ AddMonoidHom.eval rho.primitiveGenerator

@[simp]
theorem characterDivisor_apply (u : N →+ ℤ) (rho : Phi.Ray) :
    Phi.characterDivisor u rho = u rho.primitiveGenerator :=
  (rfl)

/-! ### Global character weights -/

/-- The character weights of the invariant divisor with ray coefficients `a`: the integral
characters `u` with `u v_ρ ≥ -a ρ` for the primitive generator `v_ρ` of every ray `ρ`. -/
def divisorWeights (a : Phi.Ray → ℤ) : Set (N →+ ℤ) :=
  {u | ∀ rho, -a rho ≤ u rho.primitiveGenerator}

variable {Phi}

@[simp]
theorem mem_divisorWeights {a : Phi.Ray → ℤ} {u : N →+ ℤ} :
    u ∈ Phi.divisorWeights a ↔ ∀ rho, -a rho ≤ u rho.primitiveGenerator :=
  Iff.rfl

/-- Membership in the character weights is the nonnegativity of `u v_ρ + a ρ` at every ray. -/
theorem mem_divisorWeights_iff_add_nonneg {a : Phi.Ray → ℤ} {u : N →+ ℤ} :
    u ∈ Phi.divisorWeights a ↔ ∀ rho, 0 ≤ u rho.primitiveGenerator + a rho := by
  simp only [mem_divisorWeights, neg_le_iff_add_nonneg]

/-- The trivial character is a weight exactly when the divisor is effective. -/
theorem zero_mem_divisorWeights_iff {a : Phi.Ray → ℤ} : 0 ∈ Phi.divisorWeights a ↔ 0 ≤ a := by
  simp [Pi.le_def]

/-- Enlarging the divisor enlarges its character weights. -/
@[gcongr]
theorem divisorWeights_mono {a b : Phi.Ray → ℤ} (h : a ≤ b) :
    Phi.divisorWeights a ⊆ Phi.divisorWeights b :=
  fun _ hu rho ↦ (neg_le_neg (h rho)).trans (hu rho)

/-- A fan without rays imposes no conditions: every character is a weight. -/
@[simp]
theorem divisorWeights_of_isEmpty [IsEmpty Phi.Ray] (a : Phi.Ray → ℤ) :
    Phi.divisorWeights a = Set.univ :=
  Set.eq_univ_of_forall fun _ rho ↦ isEmptyElim rho

/-- `u` is a weight of `D + div χ ^ m` exactly when `u + m` is a weight of `D`. -/
theorem mem_divisorWeights_add_characterDivisor {a : Phi.Ray → ℤ} {m u : N →+ ℤ} :
    u ∈ Phi.divisorWeights (a + Phi.characterDivisor m) ↔ u + m ∈ Phi.divisorWeights a := by
  simp only [mem_divisorWeights, Pi.add_apply, characterDivisor_apply, AddMonoidHom.add_apply]
  exact forall_congr' fun _ ↦ by omega

/-- Adding the divisor of the character `χ ^ m` translates the character weights by `-m`. -/
theorem divisorWeights_add_characterDivisor (a : Phi.Ray → ℤ) (m : N →+ ℤ) :
    Phi.divisorWeights (a + Phi.characterDivisor m) = -m +ᵥ Phi.divisorWeights a := by
  ext u
  rw [mem_divisorWeights_add_characterDivisor, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg,
    vadd_eq_add, add_comm]

/-- The sum of weights of two divisors is a weight of their sum. -/
theorem add_mem_divisorWeights_add {a b : Phi.Ray → ℤ} {u w : N →+ ℤ}
    (hu : u ∈ Phi.divisorWeights a) (hw : w ∈ Phi.divisorWeights b) :
    u + w ∈ Phi.divisorWeights (a + b) := fun rho ↦ by
  have := hu rho
  have := hw rho
  simp only [Pi.add_apply, AddMonoidHom.add_apply]
  omega

/-- The weights of two divisors add to weights of their sum. -/
theorem divisorWeights_add_subset (a b : Phi.Ray → ℤ) :
    Phi.divisorWeights a + Phi.divisorWeights b ⊆ Phi.divisorWeights (a + b) :=
  Set.add_subset_iff.2 fun _ hu _ hw ↦ add_mem_divisorWeights_add hu hw

/-! ### Character weights on a cone -/

variable (Phi) in
/-- The character weights on the cone `σ` of the invariant divisor with ray coefficients `a`: the
integral characters `u` with `u v_ρ ≥ -a ρ` for the primitive generator `v_ρ` of every ray `ρ`
contained in `σ`. -/
def coneDivisorWeights (sigma : Phi.cones) (a : Phi.Ray → ℤ) : Set (N →+ ℤ) :=
  {u | ∀ rho : Phi.Ray, rho.toCone ≤ sigma → -a rho ≤ u rho.primitiveGenerator}

@[simp]
theorem mem_coneDivisorWeights {sigma : Phi.cones} {a : Phi.Ray → ℤ} {u : N →+ ℤ} :
    u ∈ Phi.coneDivisorWeights sigma a ↔
      ∀ rho : Phi.Ray, rho.toCone ≤ sigma → -a rho ≤ u rho.primitiveGenerator :=
  Iff.rfl

/-- Enlarging the divisor enlarges its character weights on a cone. -/
@[gcongr]
theorem coneDivisorWeights_mono (sigma : Phi.cones) {a b : Phi.Ray → ℤ} (h : a ≤ b) :
    Phi.coneDivisorWeights sigma a ⊆ Phi.coneDivisorWeights sigma b :=
  fun _ hu rho hrho ↦ (neg_le_neg (h rho)).trans (hu rho hrho)

/-- Passing to a smaller cone imposes fewer conditions and enlarges the character weights. -/
theorem coneDivisorWeights_anti {sigma tau : Phi.cones} (h : tau ≤ sigma) (a : Phi.Ray → ℤ) :
    Phi.coneDivisorWeights sigma a ⊆ Phi.coneDivisorWeights tau a :=
  fun _ hu rho hrho ↦ hu rho (hrho.trans h)

/-- The global character weights are weights on every cone. -/
theorem divisorWeights_subset_coneDivisorWeights (sigma : Phi.cones) (a : Phi.Ray → ℤ) :
    Phi.divisorWeights a ⊆ Phi.coneDivisorWeights sigma a :=
  fun _ hu rho _ ↦ hu rho

/-- The global character weights are the intersection of the character weights on the cones of
the fan: each ray is itself a cone of the fan. -/
theorem iInter_coneDivisorWeights (a : Phi.Ray → ℤ) :
    ⋂ sigma : Phi.cones, Phi.coneDivisorWeights sigma a = Phi.divisorWeights a := by
  refine Set.Subset.antisymm (fun u hu rho ↦ ?_) fun _ hu ↦
    Set.mem_iInter.2 fun sigma ↦ divisorWeights_subset_coneDivisorWeights sigma a hu
  exact Set.mem_iInter.1 hu rho.toCone rho le_rfl

/-- `u` is a weight of `D + div χ ^ m` on a cone exactly when `u + m` is a weight of `D` there. -/
theorem mem_coneDivisorWeights_add_characterDivisor {sigma : Phi.cones} {a : Phi.Ray → ℤ}
    {m u : N →+ ℤ} :
    u ∈ Phi.coneDivisorWeights sigma (a + Phi.characterDivisor m) ↔
      u + m ∈ Phi.coneDivisorWeights sigma a := by
  simp only [mem_coneDivisorWeights, Pi.add_apply, characterDivisor_apply,
    AddMonoidHom.add_apply]
  exact forall_congr' fun _ ↦ imp_congr_right fun _ ↦ by omega

/-- Adding the divisor of the character `χ ^ m` translates the character weights on a cone by
`-m`. -/
theorem coneDivisorWeights_add_characterDivisor (sigma : Phi.cones) (a : Phi.Ray → ℤ)
    (m : N →+ ℤ) :
    Phi.coneDivisorWeights sigma (a + Phi.characterDivisor m) =
      -m +ᵥ Phi.coneDivisorWeights sigma a := by
  ext u
  rw [mem_coneDivisorWeights_add_characterDivisor, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg,
    vadd_eq_add, add_comm]

/-- The sum of weights of two divisors on a cone is a weight of their sum on that cone. -/
theorem add_mem_coneDivisorWeights_add {sigma : Phi.cones} {a b : Phi.Ray → ℤ} {u w : N →+ ℤ}
    (hu : u ∈ Phi.coneDivisorWeights sigma a) (hw : w ∈ Phi.coneDivisorWeights sigma b) :
    u + w ∈ Phi.coneDivisorWeights sigma (a + b) := fun rho hrho ↦ by
  have := hu rho hrho
  have := hw rho hrho
  simp only [Pi.add_apply, AddMonoidHom.add_apply]
  omega

/-- The weights of two divisors on a cone add to weights of their sum on that cone. -/
theorem coneDivisorWeights_add_subset (sigma : Phi.cones) (a b : Phi.Ray → ℤ) :
    Phi.coneDivisorWeights sigma a + Phi.coneDivisorWeights sigma b ⊆
      Phi.coneDivisorWeights sigma (a + b) :=
  Set.add_subset_iff.2 fun _ hu _ hw ↦ add_mem_coneDivisorWeights_add hu hw

/-- The character weights on a cone are stable under adding characters of the dual semigroup of
the cone. -/
theorem add_mem_coneDivisorWeights {sigma : Phi.cones} {a : Phi.Ray → ℤ} {u p : N →+ ℤ}
    (hu : u ∈ Phi.coneDivisorWeights sigma a) (hp : p ∈ dualSemigroup Phi.lattice sigma.val) :
    u + p ∈ Phi.coneDivisorWeights sigma a := fun rho hrho ↦ by
  have := hu rho hrho
  have := (Phi.mem_dualSemigroup_iff_forall_ray_le sigma p).1 hp rho hrho
  rw [AddMonoidHom.add_apply]
  omega

/-- The sum of the dual semigroup and the divisor weights is contained in the weights. -/
theorem dualSemigroup_add_coneDivisorWeights_subset (sigma : Phi.cones)
    (a : Phi.Ray → ℤ) :
    (dualSemigroup Phi.lattice sigma.val : Set (N →+ ℤ)) + Phi.coneDivisorWeights sigma a ⊆
      Phi.coneDivisorWeights sigma a :=
  Set.add_subset_iff.2 fun u hu w hw ↦ by
    simpa only [add_comm] using add_mem_coneDivisorWeights hw hu

/-- The character weights of the zero divisor on a cone are its dual semigroup. -/
@[simp]
theorem coneDivisorWeights_zero (sigma : Phi.cones) :
    Phi.coneDivisorWeights sigma 0 = dualSemigroup Phi.lattice sigma.val := by
  ext u
  rw [SetLike.mem_coe, mem_dualSemigroup_iff_forall_ray_le, mem_coneDivisorWeights]
  simp only [Pi.zero_apply, neg_zero]

/-- If `m` satisfies the Cartier equations `m v_ρ = -a ρ` on the rays of a cone, then the character
weights on that cone are the translate of its dual semigroup by `m`. -/
theorem coneDivisorWeights_eq_vadd {sigma : Phi.cones} {a : Phi.Ray → ℤ} {m : N →+ ℤ}
    (hm : ∀ rho : Phi.Ray, rho.toCone ≤ sigma → m rho.primitiveGenerator = -a rho) :
    Phi.coneDivisorWeights sigma a = m +ᵥ (dualSemigroup Phi.lattice sigma.val : Set (N →+ ℤ)) := by
  ext u
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, SetLike.mem_coe, mem_dualSemigroup_iff_forall_ray_le,
    mem_coneDivisorWeights]
  refine forall_congr' fun rho ↦ imp_congr_right fun hrho ↦ ?_
  rw [vadd_eq_add, AddMonoidHom.add_apply, AddMonoidHom.neg_apply, ← hm rho hrho]
  omega

/-- On a regular cone the Cartier equations `m v_ρ = -a ρ` on the rays of the cone have an integral
solution, because the primitive ray generators extend to an integral basis of the lattice. -/
theorem exists_forall_ray_le_eq_neg {sigma : Phi.cones} (hsigma : IsRegularCone i sigma.val)
    (a : Phi.Ray → ℤ) :
    ∃ m : N →+ ℤ, ∀ rho : Phi.Ray, rho.toCone ≤ sigma → m rho.primitiveGenerator = -a rho := by
  obtain ⟨n, b, r, hb⟩ := hsigma.exists_basis
  let g : ToricRay sigma.val → ℤ := fun rho ↦ -a (Ray.ofToricRay Phi sigma rho)
  refine ⟨(b.constr ℤ (Function.extend r g 0)).toAddMonoidHom, fun rho hrho ↦ ?_⟩
  -- The basis vector at the index of the ray is the primitive generator of the fan ray.
  have hgen : b (r (rho.toToricRay Phi sigma hrho)) = rho.primitiveGenerator := by
    rw [(hb.isPrimitiveGenerator_apply _).eq_primitiveGenerator Phi.lattice
      hsigma.toIsToricCone, Ray.primitiveGenerator_toToricRay]
  rw [← hgen, LinearMap.toAddMonoidHom_coe, Module.Basis.constr_basis,
    r.injective.extend_apply]
  simp only [g, Ray.ofToricRay_toToricRay]

/-- On a regular cone the character weights are a translate `m_σ + P_σ` of the dual semigroup. -/
theorem exists_coneDivisorWeights_eq_vadd {sigma : Phi.cones}
    (hsigma : IsRegularCone i sigma.val) (a : Phi.Ray → ℤ) :
    ∃ m : N →+ ℤ,
      Phi.coneDivisorWeights sigma a = m +ᵥ (dualSemigroup Phi.lattice sigma.val : Set (N →+ ℤ)) :=
  (exists_forall_ray_le_eq_neg hsigma a).imp fun _ ↦ coneDivisorWeights_eq_vadd

/-- The difference of two local Cartier characters for the same divisor belongs to the
dual semigroup of their overlap. Swapping the charts gives the inverse transition character. -/
theorem sub_mem_dualSemigroup_inf {sigma tau : Phi.cones} {a : Phi.Ray → ℤ} {m n : N →+ ℤ}
    (hm : ∀ rho : Phi.Ray, rho.toCone ≤ sigma → m rho.primitiveGenerator = -a rho)
    (hn : ∀ rho : Phi.Ray, rho.toCone ≤ tau → n rho.primitiveGenerator = -a rho) :
    m - n ∈ dualSemigroup Phi.lattice (sigma ⊓ tau).val := by
  rw [mem_dualSemigroup_iff_forall_ray_le]
  intro rho hrho
  simp [hm rho (hrho.trans inf_le_left), hn rho (hrho.trans inf_le_right)]

/-- Finite sets of weights on a face can all be moved into the larger cone's weight set by
adding the same nonnegative multiple of a character exposing the face. -/
theorem exists_nsmul_add_mem_coneDivisorWeights {sigma tau : Phi.cones} {m : N →+ ℤ}
    (hm : m ∈ dualSemigroup Phi.lattice sigma.val)
    (htau : sigma.val ⊓
      PointedCone.ofSubmodule (LinearMap.ker (Phi.lattice.realCharacter m)) = tau.val)
    {a : Phi.Ray → ℤ} (s : Finset (N →+ ℤ))
    (hs : (s : Set (N →+ ℤ)) ⊆ Phi.coneDivisorWeights tau a) :
    ∃ n : ℕ, ∀ u ∈ s, n • m + u ∈ Phi.coneDivisorWeights sigma a := by
  -- Bound all the deficits at once, using that each positive pairing is at least one.
  obtain ⟨n, hn⟩ := Finite.bddAbove_range fun p : (↑s : Set (N →+ ℤ)) × Phi.Ray ↦
    (-a p.2 - p.1.val p.2.primitiveGenerator).toNat
  refine ⟨n, fun u hu ↦ mem_coneDivisorWeights.2 fun rho hρ ↦ ?_⟩
  simp only [AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply, nsmul_eq_mul]
  by_cases hρτ : rho.toCone ≤ tau
  · have huτ := mem_coneDivisorWeights.1 (hs hu) rho hρτ
    have hmρ := (Phi.mem_dualSemigroup_iff_forall_ray_le sigma m).1 hm rho hρ
    exact huτ.trans (le_add_of_nonneg_left (mul_nonneg (Int.natCast_nonneg _) hmρ))
  · have hpos := Phi.apply_primitiveGenerator_pos_of_inf_ker_eq_face hm htau hρ hρτ
    let p : (↑s : Set (N →+ ℤ)) × Phi.Ray := (⟨u, hu⟩, rho)
    have hbound : (-a rho - u rho.primitiveGenerator).toNat ≤ n :=
      hn (Set.mem_range_self p)
    have hmul : (n : ℤ) ≤ (n : ℤ) * m rho.primitiveGenerator :=
      le_mul_of_one_le_right (Int.natCast_nonneg _) (by omega)
    omega

end TauCeti.Toric.Fan
