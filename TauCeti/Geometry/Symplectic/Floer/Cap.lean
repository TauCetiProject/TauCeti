/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Torsor.Quotient
public import TauCeti.Geometry.Symplectic.Floer.PeriodGroup
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

/-!
# Caps of contractible orbits as torsors over the period group

Let `x` be a contractible one-periodic orbit of a Hamiltonian on a closed symplectic manifold
`(X, ω)`. A *raw cap* of `x` is a homotopy class of discs bounding `x`. Gluing a sphere to a disc
makes the raw caps of `x` a torsor `P` under a group `S` of spherical classes on which the
symplectic area `ω : S →+ ℝ` and the first Chern number `c : S →+ ℤ` are defined (for instance
`π₂(X)` or its Hurewicz image). Capped Floer theory identifies two caps when the sphere obtained
by gluing them along `x` has zero area and zero first Chern number. The resulting *cap classes*
`CapClass ω c P` form a torsor under the period group `Γ = PeriodGroup ω c`; this is an instance
of the general fact that `H`-orbits in a `G`-torsor form a `G ⧸ H`-torsor
(`AddAction.orbitRel.Quotient.instAddTorsorQuotientAddGroup`).

The action `A_H(x, D) = ∫ D^* ω + ∫ H(t, x(t)) dt` and the grading `μ(x, D)` of a capped orbit
obey the *recapping laws* `A_H(x, B # D) = ω(B) + A_H(x, D)` and `μ(x, B # D) = 2 c₁(B) + μ(x, D)`.
A function on raw caps obeying such a law descends to cap classes (`CapClass.lift`), and a cap
class is determined by its action and its grading (`eq_iff_action_eq_and_index_eq`): this is
why the period group is the quotient by the joint kernel of area and Chern number.

For the pair-of-pants product, fix a homotopy class `u` of pairs of pants with input orbits
`x₁, x₂` and output orbit `x₀`. Gluing caps `D₁, D₂` of the inputs to `u` gives a cap `glue D₁ D₂`
of the output, and recapping either input recaps the glued cap by the same class. The class
`A = D₀ + u − D₁ − D₂` of the resulting product coefficient, measured against an output cap `D₀`,
is `productClass glue D₁ D₂ D₀ = D₀ -ᵥ glue D₁ D₂ ∈ Γ`. Recapping an input by `B` changes `A` by
`−B`, and recapping the output changes it by `+B`. Consequently the topological energy
`A₁(x₁, D₁) + A₂(x₂, D₂) − A₀(x₀, D₀) + ω(A)` and the index
`μ₁ + μ₂ − μ₀ + 2 c₁(A)` do not depend on the choice of caps
(`add_sub_add_map_productClass_eq`, `add_sub_add_two_mul_chern_productClass_eq`).

## Main definitions

* `TauCeti.Floer.CapClass ω c P`: cap classes, the quotient of the raw caps `P` by recapping
  with classes of zero area and zero first Chern number. It is a torsor under `PeriodGroup ω c`.
* `TauCeti.Floer.CapClass.lift`: the descent of a function on raw caps obeying a recapping law.
* `TauCeti.Floer.productClass`: the class `D₀ -ᵥ glue D₁ D₂` of a product coefficient.

## Main results

* `TauCeti.Floer.CapClass.mk_eq_mk_iff`: two raw caps have the same class exactly when they
  differ by a class of zero area and zero first Chern number, equivalently
  (`CapClass.mk_eq_mk_iff_action_eq_and_index_eq`) when they have the same action and grading.
* `TauCeti.Floer.CapClass.lift_vadd`: the descended function obeys the recapping law on cap
  classes.
* `TauCeti.Floer.eq_iff_action_eq_and_index_eq`: a cap class is determined by its action and its
  grading.
* `TauCeti.Floer.productClass_vadd_fst`, `TauCeti.Floer.productClass_vadd_snd`,
  `TauCeti.Floer.productClass_vadd_out`: the recapping laws for the product class.
* `TauCeti.Floer.productClass_eq_add_sub`: the change of reference caps for the product class.
* `TauCeti.Floer.add_sub_add_map_productClass_eq`: the cap independence of
  `f₁ + f₂ − f₀ + φ(A)` for functions `fᵢ` obeying the recapping law for `φ`; with `φ` the area
  this is the cap independence of the topological energy.
* `TauCeti.Floer.add_sub_add_two_mul_chern_productClass_eq`: the cap independence of the index
  `μ₁ + μ₂ − μ₀ + 2 c₁(A)`.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology and the pair-of-pants product.
-/

public section

namespace TauCeti.Floer

section Group

variable {S : Type*} [AddGroup S] (ω : S →+ ℝ) (c : S →+ ℤ)

/-- The cap classes of an orbit: the quotient of a torsor `P` of raw caps under the spherical
classes `S` by recapping with classes of zero area and zero first Chern number. It is a torsor
under the period group `PeriodGroup ω c`, and recapping by `γ : PeriodGroup ω c` is `γ +ᵥ D`.

It is an abbreviation so that the orbit-quotient and torsor API applies to it directly. -/
abbrev CapClass (P : Type*) [AddTorsor S P] : Type _ :=
  AddAction.orbitRel.Quotient (ω.prod c).ker P

namespace CapClass

variable {ω c} {P : Type*} [AddTorsor S P]

/-- Two raw caps have the same class exactly when they differ by a spherical class of zero area
and zero first Chern number. -/
theorem mk_eq_mk_iff {p q : P} :
    (Quotient.mk'' p : CapClass ω c P) = Quotient.mk'' q ↔ ω (p -ᵥ q) = 0 ∧ c (p -ᵥ q) = 0 := by
  rw [AddAction.orbitRel.Quotient.mk_eq_mk_iff_vsub_mem, AddMonoidHom.mem_ker,
    AddMonoidHom.prod_apply, Prod.mk_eq_zero]

variable {A : Type*} [AddMonoid A]

/-- A function `f` on raw caps that changes by `φ g` under recapping by `g`, for a homomorphism
`φ` on the period group, descends to cap classes. The action (with `φ = PeriodGroup.area ω c`)
and the grading (with `φ = 2 • PeriodGroup.chern ω c`) are the main examples. -/
def lift (φ : PeriodGroup ω c →+ A) (f : P → A)
    (hf : ∀ (g : S) (p : P), f (g +ᵥ p) = φ g + f p) : CapClass ω c P → A :=
  Quotient.lift f fun p q hpq => by
    have hk := (AddAction.orbitRel.Quotient.orbitRel_iff_vsub_mem _).1 hpq
    rw [← vsub_vadd p q, hf, (QuotientAddGroup.eq_zero_iff _).2 hk, map_zero, zero_add]

variable (φ : PeriodGroup ω c →+ A) (f : P → A) (hf : ∀ (g : S) (p : P), f (g +ᵥ p) = φ g + f p)

/-- The descended function takes the value of `f` on the class of a raw cap. -/
@[simp]
theorem lift_mk (p : P) : lift φ f hf (Quotient.mk'' p) = f p :=
  (rfl)

/-- The descended function obeys the recapping law on cap classes. -/
@[simp]
theorem lift_vadd (γ : PeriodGroup ω c) (D : CapClass ω c P) :
    lift φ f hf (γ +ᵥ D) = φ γ + lift φ f hf D := by
  induction γ using QuotientAddGroup.induction_on with | H g =>
  induction D using Quotient.inductionOn' with
  | h p => rw [AddAction.orbitRel.Quotient.mk_vadd_mk, lift_mk, lift_mk, hf]

end CapClass

section Torsor

variable {ω c} {C : Type*} [AddTorsor (PeriodGroup ω c) C]

/-- Caps are determined by their action and their grading: in a torsor `C` under the period
group, such as `CapClass ω c P`, if `a` and `m` obey the recapping laws for area and twice the
first Chern number, then two caps are equal exactly when they have the same value under both. -/
theorem eq_iff_action_eq_and_index_eq {a : C → ℝ} {m : C → ℤ}
    (ha : ∀ (γ : PeriodGroup ω c) (D : C), a (γ +ᵥ D) = PeriodGroup.area ω c γ + a D)
    (hm : ∀ (γ : PeriodGroup ω c) (D : C), m (γ +ᵥ D) = 2 * PeriodGroup.chern ω c γ + m D)
    {D D' : C} : D = D' ↔ a D = a D' ∧ m D = m D' := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨haD, hmD⟩ => ?_⟩
  have harea := ha (D -ᵥ D') D'
  have hchern := hm (D -ᵥ D') D'
  rw [vsub_vadd] at harea hchern
  rw [← vsub_eq_zero_iff_eq]
  refine PeriodGroup.ext ?_ ?_
  · rw [map_zero]
    linarith
  · rw [map_zero]
    omega

end Torsor

namespace CapClass

variable {ω c} {P : Type*} [AddTorsor S P]

/-- Two raw caps have the same class exactly when they have the same action and the same grading,
for functions `a` and `m` on raw caps obeying the recapping laws for area and twice the first
Chern number. -/
theorem mk_eq_mk_iff_action_eq_and_index_eq {a : P → ℝ} {m : P → ℤ}
    (ha : ∀ (g : S) (p : P), a (g +ᵥ p) = ω g + a p)
    (hm : ∀ (g : S) (p : P), m (g +ᵥ p) = 2 * c g + m p) {p q : P} :
    (Quotient.mk'' p : CapClass ω c P) = Quotient.mk'' q ↔ a p = a q ∧ m p = m q := by
  have ha' : ∀ (g : S) (p : P), a (g +ᵥ p) = PeriodGroup.area ω c g + a p := by
    simpa only [PeriodGroup.area_mk] using ha
  have hm' : ∀ (g : S) (p : P), m (g +ᵥ p) = ((2 : ℤ) • PeriodGroup.chern ω c) g + m p := by
    simpa only [AddMonoidHom.zsmul_apply, PeriodGroup.chern_mk, smul_eq_mul] using hm
  -- `lift_mk` holds by definition, so the torsor statement for the lifts is the claim.
  exact eq_iff_action_eq_and_index_eq (lift_vadd _ a ha')
    (fun γ D => by simpa only [AddMonoidHom.zsmul_apply, smul_eq_mul] using lift_vadd _ m hm' γ D)

end CapClass

section Product

variable {ω c} {C₁ C₂ C₀ : Type*} [AddTorsor (PeriodGroup ω c) C₀]

/-- The class `A = D₀ + u − D₁ − D₂` of a product coefficient. Here `glue D₁ D₂` is the cap of
the output orbit obtained by gluing input caps `D₁` and `D₂` to a fixed pair of pants `u`, and
`D₀` is the chosen output cap. In a reference-output basis the coefficient is weighted by the
Novikov monomial of `-A`. -/
def productClass (glue : C₁ → C₂ → C₀) (D₁ : C₁) (D₂ : C₂) (D₀ : C₀) : PeriodGroup ω c :=
  D₀ -ᵥ glue D₁ D₂

variable {glue : C₁ → C₂ → C₀}

/-- The product class is the difference of the output cap and the glued cap. -/
theorem productClass_def (D₁ : C₁) (D₂ : C₂) (D₀ : C₀) :
    productClass glue D₁ D₂ D₀ = D₀ -ᵥ glue D₁ D₂ :=
  (rfl)

/-- The product class vanishes exactly when the output cap is the glued cap. -/
@[simp]
theorem productClass_eq_zero_iff {D₁ : C₁} {D₂ : C₂} {D₀ : C₀} :
    productClass glue D₁ D₂ D₀ = 0 ↔ D₀ = glue D₁ D₂ := by
  rw [productClass_def, vsub_eq_zero_iff_eq]

/-- Recapping the output by `γ` adds `γ` to the product class. -/
@[simp]
theorem productClass_vadd_out (γ : PeriodGroup ω c) (D₁ : C₁) (D₂ : C₂) (D₀ : C₀) :
    productClass glue D₁ D₂ (γ +ᵥ D₀) = γ + productClass glue D₁ D₂ D₀ := by
  rw [productClass_def, productClass_def, vadd_vsub_assoc]

/-- If gluing is equivariant in the first input, recapping the first input by `γ` subtracts `γ`
from the product class. -/
theorem productClass_vadd_fst [VAdd (PeriodGroup ω c) C₁]
    (hglue : ∀ (γ : PeriodGroup ω c) D₁ D₂, glue (γ +ᵥ D₁) D₂ = γ +ᵥ glue D₁ D₂)
    (γ : PeriodGroup ω c) (D₁ : C₁) (D₂ : C₂) (D₀ : C₀) :
    productClass glue (γ +ᵥ D₁) D₂ D₀ = productClass glue D₁ D₂ D₀ - γ := by
  rw [productClass_def, hglue, vsub_vadd_eq_vsub_sub, productClass_def]

/-- If gluing is equivariant in the second input, recapping the second input by `γ` subtracts
`γ` from the product class. -/
theorem productClass_vadd_snd [VAdd (PeriodGroup ω c) C₂]
    (hglue : ∀ (γ : PeriodGroup ω c) D₁ D₂, glue D₁ (γ +ᵥ D₂) = γ +ᵥ glue D₁ D₂)
    (γ : PeriodGroup ω c) (D₁ : C₁) (D₂ : C₂) (D₀ : C₀) :
    productClass glue D₁ (γ +ᵥ D₂) D₀ = productClass glue D₁ D₂ D₀ - γ := by
  rw [productClass_def, hglue, vsub_vadd_eq_vsub_sub, productClass_def]

variable [AddTorsor (PeriodGroup ω c) C₁] [AddTorsor (PeriodGroup ω c) C₂]

/-- Change of reference caps: if gluing is equivariant in each input, the product class for caps
`Dᵢ` is the product class for reference caps `rᵢ`, plus the recapping class of the output, minus
the recapping classes of the inputs. -/
theorem productClass_eq_add_sub
    (hglue₁ : ∀ (γ : PeriodGroup ω c) D₁ D₂, glue (γ +ᵥ D₁) D₂ = γ +ᵥ glue D₁ D₂)
    (hglue₂ : ∀ (γ : PeriodGroup ω c) D₁ D₂, glue D₁ (γ +ᵥ D₂) = γ +ᵥ glue D₁ D₂)
    (D₁ r₁ : C₁) (D₂ r₂ : C₂) (D₀ r₀ : C₀) :
    productClass glue D₁ D₂ D₀ =
      productClass glue r₁ r₂ r₀ + (D₀ -ᵥ r₀) - (D₁ -ᵥ r₁) - (D₂ -ᵥ r₂) := by
  conv_lhs => rw [← vsub_vadd D₁ r₁, ← vsub_vadd D₂ r₂, ← vsub_vadd D₀ r₀]
  rw [productClass_vadd_out, productClass_vadd_fst hglue₁, productClass_vadd_snd hglue₂]
  -- `PeriodGroup ω c` has no commutative instance for a general `S`, so compare areas and
  -- Chern numbers.
  refine PeriodGroup.ext ?_ ?_ <;> simp only [map_add, map_sub] <;> abel

/-- Cap independence of `f₁ D₁ + f₂ D₂ − f₀ D₀ + φ(A)`: if gluing is equivariant in each input
and the functions `fᵢ` change by `φ γ` under recapping by `γ`, then this quantity takes the same
value for all choices of caps. With `φ = PeriodGroup.area ω c` and the action functionals as
`fᵢ`, this is the cap independence of the topological energy
`A₁(D₁) + A₂(D₂) − A₀(D₀) + ω(A)` of a product coefficient. -/
theorem add_sub_add_map_productClass_eq {A : Type*} [AddCommGroup A]
    (φ : PeriodGroup ω c →+ A) {f₁ : C₁ → A} {f₂ : C₂ → A} {f₀ : C₀ → A}
    (hglue₁ : ∀ (γ : PeriodGroup ω c) D₁ D₂, glue (γ +ᵥ D₁) D₂ = γ +ᵥ glue D₁ D₂)
    (hglue₂ : ∀ (γ : PeriodGroup ω c) D₁ D₂, glue D₁ (γ +ᵥ D₂) = γ +ᵥ glue D₁ D₂)
    (hf₁ : ∀ (γ : PeriodGroup ω c) D, f₁ (γ +ᵥ D) = φ γ + f₁ D)
    (hf₂ : ∀ (γ : PeriodGroup ω c) D, f₂ (γ +ᵥ D) = φ γ + f₂ D)
    (hf₀ : ∀ (γ : PeriodGroup ω c) D, f₀ (γ +ᵥ D) = φ γ + f₀ D)
    (D₁ D₁' : C₁) (D₂ D₂' : C₂) (D₀ D₀' : C₀) :
    f₁ D₁ + f₂ D₂ - f₀ D₀ + φ (productClass glue D₁ D₂ D₀) =
      f₁ D₁' + f₂ D₂' - f₀ D₀' + φ (productClass glue D₁' D₂' D₀') := by
  rw [← vsub_vadd D₁ D₁', ← vsub_vadd D₂ D₂', ← vsub_vadd D₀ D₀', productClass_vadd_out,
    productClass_vadd_fst hglue₁, productClass_vadd_snd hglue₂, hf₁, hf₂, hf₀]
  simp only [map_add, map_sub]
  abel

/-- Cap independence of the index `μ₁(D₁) + μ₂(D₂) − μ₀(D₀) + 2 c₁(A)` of a product coefficient,
for gradings `mᵢ` obeying the recapping law for twice the first Chern number. The Fredholm index
of a pair of pants in class `A` is this quantity minus half the dimension of the target. -/
theorem add_sub_add_two_mul_chern_productClass_eq {m₁ : C₁ → ℤ} {m₂ : C₂ → ℤ} {m₀ : C₀ → ℤ}
    (hglue₁ : ∀ (γ : PeriodGroup ω c) D₁ D₂, glue (γ +ᵥ D₁) D₂ = γ +ᵥ glue D₁ D₂)
    (hglue₂ : ∀ (γ : PeriodGroup ω c) D₁ D₂, glue D₁ (γ +ᵥ D₂) = γ +ᵥ glue D₁ D₂)
    (hm₁ : ∀ (γ : PeriodGroup ω c) D, m₁ (γ +ᵥ D) = 2 * PeriodGroup.chern ω c γ + m₁ D)
    (hm₂ : ∀ (γ : PeriodGroup ω c) D, m₂ (γ +ᵥ D) = 2 * PeriodGroup.chern ω c γ + m₂ D)
    (hm₀ : ∀ (γ : PeriodGroup ω c) D, m₀ (γ +ᵥ D) = 2 * PeriodGroup.chern ω c γ + m₀ D)
    (D₁ D₁' : C₁) (D₂ D₂' : C₂) (D₀ D₀' : C₀) :
    m₁ D₁ + m₂ D₂ - m₀ D₀ + 2 * PeriodGroup.chern ω c (productClass glue D₁ D₂ D₀) =
      m₁ D₁' + m₂ D₂' - m₀ D₀' + 2 * PeriodGroup.chern ω c (productClass glue D₁' D₂' D₀') := by
  have key := add_sub_add_map_productClass_eq ((2 : ℤ) • PeriodGroup.chern ω c) hglue₁ hglue₂
    (by simpa using hm₁) (by simpa using hm₂) (by simpa using hm₀) D₁ D₁' D₂ D₂' D₀ D₀'
  simpa only [AddMonoidHom.zsmul_apply, Int.zsmul_eq_mul] using key

end Product

end Group

end TauCeti.Floer
