/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.Induction.Mackey.Subgroup
public import TauCeti.RepresentationTheory.RelativeNorm

/-!
# Level forms

Let `G` be a group, `Γ` and `J` subgroups of `G`, and `M` a module with a right action of `J`,
written `m ∣ u`. Encode the right action as a representation `ρ` of the opposite group `Jᵐᵒᵖ`,
so that `m ∣ u = ρ (op u) m` and `(m ∣ u) ∣ v = m ∣ (u * v)`. The module of **level forms**

`S_Γ(J, M) = {f : G → M | f (γ * g * u) = f g ∣ u for all γ ∈ Γ, g ∈ G, u ∈ J}`

is `Representation.levelForms ρ Γ`. It is the common carrier of algebraic modular forms on a
reductive group which is compact at infinity (`G` the finite-adelic points, `Γ` the rational
points, `J` a compact open level) and of quaternionic forms of any weight on a definite quaternion
algebra, with algebraic, analytic or integral coefficients. Nothing here uses topology or
finiteness of class sets or stabilizers: everything follows from the covariance law alone.

## Main definitions and results

* `Representation.levelForms ρ Γ`: the submodule `S_Γ(J, M)` of `G → M`.
* `Representation.levelAction ρ`: the left action `(u • f) g = f (g * u) ∣ u⁻¹` of `J` on
  `G → M`; a level form is a `Γ`-invariant function fixed by it
  (`Representation.mem_levelForms_iff_levelAction`).
* `Representation.levelFormsEquivPi`: **evaluation at representatives**. For representatives
  `c q` of the double cosets `q ∈ Γ \ G / J`, `f ↦ (f (c q))_q` is a linear equivalence from
  `S_Γ(J, M)` onto the product of the invariants `M ^ (J ∩ (c q)⁻¹ Γ (c q))`, where the stabilizer
  `J ∩ (c q)⁻¹ Γ (c q)` of the coset `Γ * c q` is the Mackey subgroup
  `TauCeti.mackeySubgroup (c q)⁻¹ Γ J` read inside `J`. Its inverse sends
  `m` to the form with value `m q ∣ u` at `γ * c q * u`, which is independent of the
  factorization because `m q` is invariant under the stabilizer; membership in these invariants
  is unpacked by `Representation.mem_invariants_mackeySubgroup_iff`.
* `Representation.levelFormsMap`: the map on level forms induced by a `J`-equivariant map of
  coefficients.
* `Representation.levelFormsRes`: for `J' ≤ J`, restriction `S_Γ(J, M) → S_Γ(J', M)`, the
  identity on functions; restrictions compose (`Representation.levelFormsRes_comp`).
* `Representation.levelFormsTrace`: for `J' ≤ J` of finite index, the trace
  `(tr f) g = ∑_{u J' ∈ J / J'} f (g * u) ∣ u⁻¹`, summed over the left cosets of `J'` in `J`: the
  relative norm `Representation.relNorm` of `levelAction ρ`. It is independent of the
  representatives (`Representation.levelFormsTrace_apply`).
* `Representation.levelFormsTrace_levelFormsRes`: `tr ∘ res = [J : J'] • id`.

## References

* G. Boxer, F. Calegari, T. Gee, V. Pilloni, *Modularity theorems for abelian surfaces*,
  §5.7.2, for the arithmetic carrier `S(U, A)` with `f (g * u) = u⁻¹ f g`.
* D. Loeffler, *Overconvergent algebraic automorphic forms*, Proc. LMS 102 (2011),
  Definition 3.3.2 and Proposition 3.3.3, for module-valued forms and the evaluation
  isomorphism onto invariants of the arithmetic stabilizers.
* B. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), §§4–6.
-/

public section

open MulOpposite
open TauCeti (mackeySubgroup mem_mackeySubgroup_iff)

namespace Representation

/-- For a representation of an opposite group, read as a right action `m ∣ u = ρ (op u) m`, the
action composes as `(m ∣ u) ∣ v = m ∣ (u * v)`. -/
theorem apply_op_apply_op {R H M : Type*} [Semiring R] [Monoid H] [AddCommMonoid M] [Module R M]
    (ρ : Representation R Hᵐᵒᵖ M) (u v : H) (m : M) :
    ρ (op v) (ρ (op u) m) = ρ (op (u * v)) m := by
  rw [op_mul, map_mul, mul_apply_eq_comp]

variable {G : Type*} [Group G] {J : Subgroup G}

section Carrier

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (ρ : Representation R Jᵐᵒᵖ M) (Γ : Subgroup G)

/-- **Level forms.** For a right action `m ∣ u = ρ (op u) m` of a subgroup `J` of `G` on `M`, and
a subgroup `Γ` of `G`, the submodule of functions `f : G → M` that are invariant under left
multiplication by `Γ` and satisfy `f (g * u) = f g ∣ u` for `u ∈ J`. -/
def levelForms : Submodule R (G → M) where
  carrier := {f | (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) ∧ ∀ (u : J) g, f (g * u) = ρ (op u) (f g)}
  add_mem' {f₁ f₂} h₁ h₂ :=
    ⟨fun γ hγ g ↦ by simp [h₁.1 γ hγ g, h₂.1 γ hγ g],
      fun u g ↦ by simp [h₁.2 u g, h₂.2 u g]⟩
  zero_mem' := ⟨fun _ _ _ ↦ rfl, fun _ _ ↦ by simp⟩
  smul_mem' r f hf :=
    ⟨fun γ hγ g ↦ by simp [hf.1 γ hγ g], fun u g ↦ by simp [hf.2 u g]⟩

variable {ρ Γ} in
@[simp]
theorem mem_levelForms_iff {f : G → M} :
    f ∈ ρ.levelForms Γ ↔
      (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) ∧ ∀ (u : J) g, f (g * u) = ρ (op u) (f g) :=
  Iff.rfl

/-- The left action of the level `J` on functions `G → M` that combines right translation with
the inverse coefficient action: `(u • f) g = f (g * u) ∣ u⁻¹`. The level forms are the
`Γ`-invariant functions fixed by it (`mem_levelForms_iff_levelAction`). -/
def levelAction : Representation R J (G → M) where
  toFun u :=
    { toFun f g := ρ (op u⁻¹) (f (g * u))
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  map_one' := by ext; simp
  map_mul' u v := by
    ext f g
    simp [mul_assoc]

variable {ρ Γ}

@[simp]
theorem levelAction_apply (u : J) (f : G → M) (g : G) :
    levelAction ρ u f g = ρ (op u⁻¹) (f (g * u)) :=
  (rfl)

/-- A function is fixed by `u` under `levelAction ρ` exactly when `f (g * u) = f g ∣ u`. -/
theorem levelAction_apply_eq_self_iff {f : G → M} (u : J) :
    levelAction ρ u f = f ↔ ∀ g, f (g * u) = ρ (op u) (f g) := by
  refine ⟨fun h g ↦ ?_, fun h ↦ funext fun g ↦ ?_⟩
  · conv_rhs => rw [← h]
    simp
  · simp [h]

/-- The level forms are the `Γ`-invariant functions fixed by `levelAction ρ`. -/
theorem mem_levelForms_iff_levelAction {f : G → M} :
    f ∈ ρ.levelForms Γ ↔ (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) ∧ ∀ u : J, levelAction ρ u f = f := by
  simp only [mem_levelForms_iff, levelAction_apply_eq_self_iff]

/-- With coefficients in a subsingleton module, there are no nonzero level forms. -/
theorem levelForms_eq_bot [Subsingleton M] : ρ.levelForms Γ = ⊥ :=
  Submodule.eq_bot_of_subsingleton

/-- A level form is invariant under left multiplication by `Γ`. -/
theorem levelForms_apply_mul_left (f : ρ.levelForms Γ) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    (f : G → M) (γ * g) = (f : G → M) g :=
  f.property.1 γ hγ g

/-- A level form transforms under right multiplication by the level through the coefficient
action: `f (g * u) = f g ∣ u`. -/
theorem levelForms_apply_mul_right (f : ρ.levelForms Γ) (u : J) (g : G) :
    (f : G → M) (g * u) = ρ (op u) ((f : G → M) g) :=
  f.property.2 u g

end Carrier

/-! ### Evaluation at double coset representatives -/

section Evaluation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {ρ : Representation R Jᵐᵒᵖ M} {Γ : Subgroup G}

/-- A vector is fixed by the Mackey subgroup `J ∩ s Γ s⁻¹`, read inside `J` and acting through
the level, exactly when `m ∣ u = m` for every `u ∈ J` with `s⁻¹ * u * s ∈ Γ`. At `s = c⁻¹` this is
the stabilizer `J ∩ c⁻¹ Γ c` of the coset `Γ * c`. -/
theorem mem_invariants_mackeySubgroup_iff {s : G} {m : M} :
    m ∈ invariants (ρ.comp (MonoidHom.op ((mackeySubgroup s Γ J).subgroupOf J).subtype)) ↔
      ∀ u : J, s⁻¹ * u * s ∈ Γ → ρ (op u) m = m := by
  rw [mem_invariants]
  exact ⟨fun h u hu ↦ h (op ⟨u, mem_mackeySubgroup_iff.mpr ⟨u.property, hu⟩⟩),
    fun h u ↦ h u.unop (mem_mackeySubgroup_iff.mp u.unop.property).2⟩

/-- If `m` is fixed by the stabilizer `J ∩ c⁻¹ Γ c` of `c`, then `m ∣ u` depends only on
`γ * c * u` for `γ ∈ Γ` and `u ∈ J`. -/
private theorem apply_eq_of_mul_mul_eq {c : G} {m : M}
    (hm : m ∈ invariants (ρ.comp (MonoidHom.op ((mackeySubgroup c⁻¹ Γ J).subgroupOf J).subtype)))
    {γ γ' : G} (hγ : γ ∈ Γ) (hγ' : γ' ∈ Γ) {u u' : J} (h : γ * c * u = γ' * c * u') :
    ρ (op u) m = ρ (op u') m := by
  have hs : c * ((u * u'⁻¹ : J) : G) * c⁻¹ = γ⁻¹ * γ' := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, show c * ((u : G) * (u' : G)⁻¹) * c⁻¹ =
      γ⁻¹ * (γ * c * u) * ((u' : G)⁻¹ * c⁻¹) by group, h]
    group
  calc ρ (op u) m = ρ (op u') (ρ (op (u * u'⁻¹)) m) := by
        rw [apply_op_apply_op, inv_mul_cancel_right]
    _ = ρ (op u') m := by
        rw [mem_invariants_mackeySubgroup_iff.mp hm _
          (by rw [inv_inv, hs]; exact Γ.mul_mem (Γ.inv_mem hγ) hγ')]

variable (c : DoubleCoset.Quotient (Γ : Set G) J → G)
  (hc : ∀ q, DoubleCoset.mk Γ J (c q) = q)

include hc in
private theorem exists_eq_mul_mul (g : G) :
    ∃ p : Γ × J, g = p.1 * c (DoubleCoset.mk Γ J g) * p.2 := by
  obtain ⟨γ, hγ, u, hu, h⟩ := DoubleCoset.eq.mp (hc (DoubleCoset.mk Γ J g))
  exact ⟨(⟨γ, hγ⟩, ⟨u, hu⟩), h⟩

/-- The function reconstructed from its values `m q` at the representatives `c q`: its value at
`g = γ * c q * u` is `m q ∣ u`, for one chosen factorization. -/
private noncomputable def ofPi
    (m : (q : DoubleCoset.Quotient (Γ : Set G) J) →
      invariants (ρ.comp (MonoidHom.op ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J).subtype)))
    (g : G) : M :=
  ρ (op (exists_eq_mul_mul c hc g).choose.2) (m (DoubleCoset.mk Γ J g))

include hc in
private theorem ofPi_eq
    (m : (q : DoubleCoset.Quotient (Γ : Set G) J) →
      invariants (ρ.comp (MonoidHom.op ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J).subtype)))
    {g : G} {q : DoubleCoset.Quotient (Γ : Set G) J} {γ : G} (hγ : γ ∈ Γ) (u : J)
    (hg : g = γ * c q * u) :
    ofPi c hc m g = ρ (op u) (m q) := by
  have hq : DoubleCoset.mk Γ J g = q :=
    (DoubleCoset.eq.mpr ⟨γ, hγ, u, u.property, hg⟩).symm.trans (hc q)
  subst hq
  have hch := (exists_eq_mul_mul c hc g).choose_spec
  exact apply_eq_of_mul_mul_eq (m _).property (exists_eq_mul_mul c hc g).choose.1.property hγ
    (hch.symm.trans hg)

/-- The values `f (c q)` of a level form at the representatives, each fixed by its stabilizer. -/
private def evalPi (f : ρ.levelForms Γ) (q : DoubleCoset.Quotient (Γ : Set G) J) :
    invariants (ρ.comp (MonoidHom.op ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J).subtype)) :=
  ⟨(f : G → M) (c q), mem_invariants_mackeySubgroup_iff.mpr fun u hu ↦ by
    rw [inv_inv] at hu
    rw [← levelForms_apply_mul_right f]
    conv_rhs => rw [← levelForms_apply_mul_left f hu]
    group⟩

private theorem coe_evalPi (f : ρ.levelForms Γ) (q : DoubleCoset.Quotient (Γ : Set G) J) :
    (evalPi c f q : M) = (f : G → M) (c q) :=
  rfl

variable (ρ Γ) in
/-- **Evaluation at double coset representatives.** For representatives `c q` of the double
cosets `q ∈ Γ \ G / J`, evaluation `f ↦ (f (c q))_q` identifies the level forms with the product
over `q` of the invariants of the stabilizer `J ∩ (c q)⁻¹ Γ (c q)`, acting on `M` through the
level. The inverse sends `m` to the form with value `m q ∣ u` at `γ * c q * u`
(`levelFormsEquivPi_symm_apply`). No finiteness of the double coset space or of the stabilizers
is needed. -/
noncomputable def levelFormsEquivPi :
    ρ.levelForms Γ ≃ₗ[R] ((q : DoubleCoset.Quotient (Γ : Set G) J) →
      invariants (ρ.comp (MonoidHom.op ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J).subtype)))
    where
  toFun := evalPi c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := ⟨ofPi c hc m, by
    refine ⟨fun γ hγ g ↦ ?_, fun u g ↦ ?_⟩ <;>
      obtain ⟨⟨⟨γ₀, hγ₀⟩, u₀⟩, h₀ : g = γ₀ * _ * u₀⟩ := exists_eq_mul_mul c hc g
    · rw [ofPi_eq c hc m hγ₀ u₀ h₀, ofPi_eq c hc m (q := DoubleCoset.mk Γ J g)
        (Γ.mul_mem hγ hγ₀) u₀ (by (conv_lhs => rw [h₀]); simp only [mul_assoc])]
    · rw [ofPi_eq c hc m hγ₀ u₀ h₀, ofPi_eq c hc m (q := DoubleCoset.mk Γ J g) hγ₀ (u₀ * u)
        (by (conv_lhs => rw [h₀]); simp only [Subgroup.coe_mul, mul_assoc]), apply_op_apply_op]⟩
  left_inv f := by
    ext g
    obtain ⟨⟨⟨γ₀, hγ₀⟩, u₀⟩, h₀ : g = γ₀ * _ * u₀⟩ := exists_eq_mul_mul c hc g
    refine (ofPi_eq c hc (evalPi c f) hγ₀ u₀ h₀).trans ?_
    conv_rhs => rw [h₀, levelForms_apply_mul_right f, levelForms_apply_mul_left f hγ₀]
    rw [coe_evalPi]
  right_inv m := by
    ext q
    exact (ofPi_eq c hc m (q := q) Γ.one_mem 1 (by simp)).trans (by simp)

@[simp]
theorem coe_levelFormsEquivPi_apply (f : ρ.levelForms Γ)
    (q : DoubleCoset.Quotient (Γ : Set G) J) :
    (levelFormsEquivPi ρ Γ c hc f q : M) = (f : G → M) (c q) :=
  (rfl)

/-- The level form with prescribed values `m q` at the representatives `c q` takes the value
`m q ∣ u` at `γ * c q * u`, whatever the factorization. -/
theorem levelFormsEquivPi_symm_apply
    (m : (q : DoubleCoset.Quotient (Γ : Set G) J) →
      invariants (ρ.comp (MonoidHom.op ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J).subtype)))
    (q : DoubleCoset.Quotient (Γ : Set G) J) {γ : G} (hγ : γ ∈ Γ) (u : J) :
    ((levelFormsEquivPi ρ Γ c hc).symm m : G → M) (γ * c q * u) = ρ (op u) (m q) :=
  ofPi_eq c hc m hγ u rfl

include hc in
/-- A level form is determined by its values at a set of representatives of `Γ \ G / J`. -/
theorem levelForms_ext {f f' : ρ.levelForms Γ}
    (h : ∀ q, (f : G → M) (c q) = (f' : G → M) (c q)) :
    f = f' :=
  (levelFormsEquivPi ρ Γ c hc).injective (funext fun q ↦ Subtype.ext (h q))

end Evaluation

/-! ### Coefficient maps -/

section Map

variable {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
variable {ρ : Representation R Jᵐᵒᵖ M} {σ : Representation R Jᵐᵒᵖ N}
  {τ : Representation R Jᵐᵒᵖ P} (Γ : Subgroup G)

/-- The map on level forms induced by a `J`-equivariant map of coefficients, `f ↦ φ ∘ f`. -/
def levelFormsMap (φ : IntertwiningMap ρ σ) : ρ.levelForms Γ →ₗ[R] σ.levelForms Γ where
  toFun f := ⟨φ ∘ f, fun γ hγ g ↦ by simp [levelForms_apply_mul_left f hγ],
    fun u g ↦ by simp [levelForms_apply_mul_right f, IntertwiningMap.isIntertwining]⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem coe_levelFormsMap_apply (φ : IntertwiningMap ρ σ) (f : ρ.levelForms Γ) :
    (levelFormsMap Γ φ f : G → N) = φ ∘ f :=
  (rfl)

@[simp]
theorem levelFormsMap_id : levelFormsMap Γ (IntertwiningMap.id ρ) = LinearMap.id :=
  (rfl)

theorem levelFormsMap_comp (φ : IntertwiningMap σ τ) (ψ : IntertwiningMap ρ σ) :
    levelFormsMap Γ (φ.comp ψ) = levelFormsMap Γ φ ∘ₗ levelFormsMap Γ ψ :=
  (rfl)

end Map

/-! ### Restriction and trace between levels -/

section Level

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (ρ : Representation R Jᵐᵒᵖ M) (Γ : Subgroup G) {J' : Subgroup G} (h : J' ≤ J)

/-- Level forms of level `J` are level forms of any smaller level `J'`, for the restricted
coefficient action. -/
theorem levelForms_le_levelForms_comp :
    ρ.levelForms Γ ≤ levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ :=
  fun _ hf ↦ ⟨hf.1, fun u g ↦ hf.2 (Subgroup.inclusion h u) g⟩

/-- **Restriction** to a smaller level `J' ≤ J`; it is the identity on functions
(`coe_levelFormsRes_apply`). -/
def levelFormsRes :
    ρ.levelForms Γ →ₗ[R] levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ :=
  Submodule.inclusion (levelForms_le_levelForms_comp ρ Γ h)

@[simp]
theorem coe_levelFormsRes_apply (f : ρ.levelForms Γ) :
    (levelFormsRes ρ Γ h f : G → M) = f :=
  (rfl)

theorem levelFormsRes_injective : Function.Injective (levelFormsRes ρ Γ h) :=
  Submodule.inclusion_injective _

/-- Restricting from `J` to `J'` and then to `J'' ≤ J'` is restricting from `J` to `J''`. -/
@[simp]
theorem levelFormsRes_comp {J'' : Subgroup G} (h' : J'' ≤ J') :
    levelFormsRes (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ h' ∘ₗ levelFormsRes ρ Γ h =
      levelFormsRes ρ Γ (h'.trans h) :=
  (rfl)

variable {ρ Γ h}

/-- A level form of the smaller level `J'` is fixed by `J' ∩ J` acting through `levelAction ρ`. -/
private theorem levelAction_apply_eq_self_of_mem {f : G → M}
    (hf : f ∈ levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ)
    (u : J'.subgroupOf J) : levelAction ρ u f = f :=
  (mem_levelForms_iff_levelAction.mp hf).2 ⟨u, Subgroup.mem_subgroupOf.mp u.property⟩

variable [J'.IsFiniteRelIndex J] (ρ Γ h)

/-- **The trace** from a level `J'` of finite index in `J` down to `J`:
`(tr f) g = ∑_{u J' ∈ J / J'} f (g * u) ∣ u⁻¹`, summed over the left cosets `u J'`. It is the
relative norm `Representation.relNorm` of `J' ∩ J` in `J` for `levelAction ρ`. The summand is
constant on each left coset, so the sum does not depend on the representatives
(`levelFormsTrace_apply`). -/
noncomputable def levelFormsTrace :
    levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ →ₗ[R] ρ.levelForms Γ :=
  letI := Fintype.ofFinite (J ⧸ J'.subgroupOf J)
  (relNorm (levelAction ρ) (J'.subgroupOf J)).restrict fun f hf ↦
    mem_levelForms_iff_levelAction.mpr ⟨fun γ hγ g ↦ by
      simp only [relNorm_apply, Finset.sum_apply, levelAction_apply, mul_assoc, hf.1 γ hγ],
      relNorm_apply_eq_self _ (levelAction_apply_eq_self_of_mem hf)⟩

/-- On underlying functions the trace is the relative norm of `levelAction ρ`, for any
`Fintype` structure on `J / J'`. -/
@[simp]
theorem coe_levelFormsTrace_apply [Fintype (J ⧸ J'.subgroupOf J)]
    (f : levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ) :
    (levelFormsTrace ρ Γ h f : G → M) = relNorm (levelAction ρ) (J'.subgroupOf J) (f : G → M) := by
  rw [levelFormsTrace, LinearMap.coe_restrict_apply]
  congr
  exact Subsingleton.elim _ _

/-- The trace `(tr f) g = ∑_{u J' ∈ J / J'} f (g * u) ∣ u⁻¹`, computed with any choice of
representatives `s x` of the left cosets `x` of `J'` in `J`. -/
theorem levelFormsTrace_apply [Fintype (J ⧸ J'.subgroupOf J)]
    (f : levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ)
    (s : J ⧸ J'.subgroupOf J → J) (hs : ∀ x, (s x : J ⧸ J'.subgroupOf J) = x) (g : G) :
    (levelFormsTrace ρ Γ h f : G → M) g = ∑ x, ρ (op (s x)⁻¹) ((f : G → M) (g * s x)) := by
  rw [coe_levelFormsTrace_apply, relNorm_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← levelAction_apply]
  exact congrFun (apply_eq_apply_of_quotientGroup_mk_eq _
    (levelAction_apply_eq_self_of_mem f.property) ((QuotientGroup.out_eq' x).trans (hs x).symm)) g

/-- **Trace after restriction is multiplication by the index**: `tr ∘ res = [J : J'] • id`. -/
@[simp]
theorem levelFormsTrace_levelFormsRes (f : ρ.levelForms Γ) :
    levelFormsTrace ρ Γ h (levelFormsRes ρ Γ h f) = J'.relIndex J • f := by
  let _ := Fintype.ofFinite (J ⧸ J'.subgroupOf J)
  refine Subtype.ext ?_
  rw [coe_levelFormsTrace_apply, coe_levelFormsRes_apply, Submodule.coe_smul_of_tower,
    relNorm_apply_of_forall_apply_eq _ (mem_levelForms_iff_levelAction.mp f.property).2,
    Subgroup.relIndex]

end Level

end Representation
