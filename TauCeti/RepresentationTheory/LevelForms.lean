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
* `Representation.levelFormsEquivPi`: **evaluation at representatives**. For representatives
  `c q` of the double cosets `q ∈ Γ \ G / J`, `f ↦ (f (c q))_q` is a linear equivalence from
  `S_Γ(J, M)` onto the product of the invariants `M ^ (J ∩ (c q)⁻¹ Γ (c q))`. Its inverse sends
  `m` to the form with value `m q ∣ u` at `γ * c q * u`, which is independent of the
  factorization because `m q` is invariant under the stabilizer.
* `Representation.levelFormsMap`: the map on level forms induced by a `J`-equivariant map of
  coefficients.
* `Representation.levelFormsRes`: for `J' ≤ J`, restriction `S_Γ(J, M) → S_Γ(J', M)`, the
  identity on functions.
* `Representation.levelFormsTrace`: for `J' ≤ J` of finite index, the trace
  `(tr f) g = ∑_{u J' ∈ J / J'} f (g * u) ∣ u⁻¹`, summed over the left cosets of `J'` in `J`; it is
  independent of the representatives (`Representation.levelFormsTrace_apply`).
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

namespace Representation

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

variable {ρ Γ}

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

/-- If `m` is fixed by the stabilizer `J ∩ c⁻¹ Γ c` of `c`, then `m ∣ u` depends only on
`γ * c * u` for `γ ∈ Γ` and `u ∈ J`. -/
private theorem apply_eq_of_mul_mul_eq {c : G} {m : M}
    (hm : m ∈ invariants
      (ρ.comp (MonoidHom.op ((Γ.comap (MulAut.conj c : G →* G)).subgroupOf J).subtype)))
    {γ γ' : G} (hγ : γ ∈ Γ) (hγ' : γ' ∈ Γ) {u u' : J} (h : γ * c * u = γ' * c * u') :
    ρ (op u) m = ρ (op u') m := by
  have hs : u * u'⁻¹ ∈ (Γ.comap (MulAut.conj c : G →* G)).subgroupOf J := by
    have : c * ((u : G) * (u' : G)⁻¹) * c⁻¹ = γ⁻¹ * γ' := by
      rw [show c * ((u : G) * (u' : G)⁻¹) * c⁻¹ = γ⁻¹ * (γ * c * u) * ((u' : G)⁻¹ * c⁻¹) by
        group, h]
      group
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.coe_ofClass,
      MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, this]
    exact Γ.mul_mem (Γ.inv_mem hγ) hγ'
  have hfix := (mem_invariants _ m).mp hm (op ⟨_, hs⟩)
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.op_apply_apply,
    MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, unop_op] at hfix
  calc ρ (op u) m = ρ (op u') (ρ (op (u * u'⁻¹)) m) := by
        rw [← mul_apply_eq_comp, ← map_mul, ← op_mul, inv_mul_cancel_right]
    _ = ρ (op u') m := by rw [hfix]

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
      invariants
        (ρ.comp (MonoidHom.op ((Γ.comap (MulAut.conj (c q) : G →* G)).subgroupOf J).subtype)))
    (g : G) : M :=
  ρ (op (exists_eq_mul_mul c hc g).choose.2) (m (DoubleCoset.mk Γ J g))

include hc in
private theorem ofPi_eq
    (m : (q : DoubleCoset.Quotient (Γ : Set G) J) →
      invariants
        (ρ.comp (MonoidHom.op ((Γ.comap (MulAut.conj (c q) : G →* G)).subgroupOf J).subtype)))
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
    invariants
      (ρ.comp (MonoidHom.op ((Γ.comap (MulAut.conj (c q) : G →* G)).subgroupOf J).subtype)) :=
  ⟨(f : G → M) (c q), (mem_invariants _ _).mpr fun u ↦ by
    have hu : c q * ((u.unop : J) : G) * (c q)⁻¹ ∈ Γ := by
      have := u.unop.property
      rwa [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.coe_ofClass,
        MulAut.conj_apply] at this
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.op_apply_apply,
      Subgroup.coe_subtype]
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
      invariants
        (ρ.comp (MonoidHom.op ((Γ.comap (MulAut.conj (c q) : G →* G)).subgroupOf J).subtype)))
    where
  toFun := evalPi c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := ⟨ofPi c hc m, by
    refine ⟨fun γ hγ g ↦ ?_, fun u g ↦ ?_⟩ <;>
      obtain ⟨⟨⟨γ₀, hγ₀⟩, u₀⟩, h₀ : g = γ₀ * _ * u₀⟩ := exists_eq_mul_mul c hc g
    · rw [ofPi_eq c hc m hγ₀ u₀ h₀, ofPi_eq c hc m (q := DoubleCoset.mk Γ J g)
        (Γ.mul_mem hγ hγ₀) u₀ (by nth_rw 1 [h₀]; simp only [mul_assoc])]
    · rw [ofPi_eq c hc m hγ₀ u₀ h₀, ofPi_eq c hc m (q := DoubleCoset.mk Γ J g) hγ₀ (u₀ * u)
        (by nth_rw 1 [h₀]; simp only [Subgroup.coe_mul, mul_assoc]),
        op_mul, map_mul, mul_apply_eq_comp]⟩
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
      invariants
        (ρ.comp (MonoidHom.op ((Γ.comap (MulAut.conj (c q) : G →* G)).subgroupOf J).subtype)))
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

variable {ρ Γ h}

variable (ρ) in
/-- The summand `f (g * u) ∣ u⁻¹` of the trace, at the chosen representative `u` of a left coset
`u J'` of `J'` in `J`. -/
private noncomputable def traceTerm (f : G → M) (g : G) (x : J ⧸ J'.subgroupOf J) : M :=
  ρ (op x.out⁻¹) (f (g * x.out))

/-- The summand `f (g * u) ∣ u⁻¹` is constant on each left coset `u J'`. -/
private theorem traceTerm_mk {f : G → M}
    (hf : f ∈ levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ) (g : G) (u : J) :
    traceTerm ρ f g (u : J ⧸ J'.subgroupOf J) = ρ (op u⁻¹) (f (g * u)) := by
  obtain ⟨w, hu⟩ := QuotientGroup.mk_out_eq_mul (J'.subgroupOf J) u
  have hw : f (g * u * (w : J)) = ρ (op (w : J)) (f (g * u)) :=
    hf.2 ⟨((w : J) : G), Subgroup.mem_subgroupOf.mp w.property⟩ (g * u)
  rw [traceTerm, hu, Subgroup.coe_mul, ← mul_assoc, hw, ← mul_apply_eq_comp, ← map_mul, ← op_mul,
    mul_inv_rev, mul_inv_cancel_left]

variable [J'.IsFiniteRelIndex J]

/-- The trace sum `∑_{u J' ∈ J / J'} f (g * u) ∣ u⁻¹`. -/
private theorem traceTerm_sum_mem {f : G → M}
    (hf : f ∈ levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ) :
    (fun g ↦ ∑ᶠ x : J ⧸ J'.subgroupOf J, traceTerm ρ f g x) ∈ ρ.levelForms Γ := by
  have := Fintype.ofFinite (J ⧸ J'.subgroupOf J)
  refine ⟨fun γ hγ g ↦ ?_, fun u g ↦ ?_⟩
  · simp only [traceTerm, mul_assoc, hf.1 γ hγ]
  · simp only [finsum_eq_sum_of_fintype, map_sum]
    refine (Fintype.sum_equiv (MulAction.toPerm u⁻¹) _ _ fun x ↦ ?_).symm
    induction x using QuotientGroup.induction_on with | H a => ?_
    rw [MulAction.toPerm_apply, MulAction.Quotient.smul_mk, traceTerm_mk hf,
      traceTerm_mk hf, ← mul_apply_eq_comp, ← map_mul, ← op_mul]
    simp [mul_assoc]

variable (ρ Γ h)

/-- **The trace** from a level `J'` of finite index in `J` down to `J`:
`(tr f) g = ∑_{u J' ∈ J / J'} f (g * u) ∣ u⁻¹`, summed over the left cosets `u J'`. The summand is
constant on each left coset, so the sum does not depend on the representatives
(`levelFormsTrace_apply`). -/
noncomputable def levelFormsTrace :
    levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ →ₗ[R] ρ.levelForms Γ where
  toFun f := ⟨fun g ↦ ∑ᶠ x : J ⧸ J'.subgroupOf J, traceTerm ρ f g x, traceTerm_sum_mem f.property⟩
  map_add' f₁ f₂ := by
    have := Fintype.ofFinite (J ⧸ J'.subgroupOf J)
    ext g
    simp [traceTerm, finsum_eq_sum_of_fintype, Finset.sum_add_distrib]
  map_smul' r f := by
    have := Fintype.ofFinite (J ⧸ J'.subgroupOf J)
    ext g
    simp [traceTerm, finsum_eq_sum_of_fintype, Finset.smul_sum]

private theorem coe_levelFormsTrace_apply_eq_finsum
    (f : levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ) (g : G) :
    (levelFormsTrace ρ Γ h f : G → M) g =
      ∑ᶠ x : J ⧸ J'.subgroupOf J, traceTerm ρ (f : G → M) g x :=
  rfl

/-- The trace `(tr f) g = ∑_{u J' ∈ J / J'} f (g * u) ∣ u⁻¹`, computed with any choice of
representatives `s x` of the left cosets `x` of `J'` in `J`. -/
theorem levelFormsTrace_apply [Fintype (J ⧸ J'.subgroupOf J)]
    (f : levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion h))) Γ)
    (s : J ⧸ J'.subgroupOf J → J) (hs : ∀ x, (s x : J ⧸ J'.subgroupOf J) = x) (g : G) :
    (levelFormsTrace ρ Γ h f : G → M) g = ∑ x, ρ (op (s x)⁻¹) ((f : G → M) (g * s x)) := by
  rw [coe_levelFormsTrace_apply_eq_finsum, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  conv_lhs => rw [← hs x]
  exact traceTerm_mk f.property g (s x)

/-- **Trace after restriction is multiplication by the index**: `tr ∘ res = [J : J'] • id`. -/
theorem levelFormsTrace_levelFormsRes (f : ρ.levelForms Γ) :
    levelFormsTrace ρ Γ h (levelFormsRes ρ Γ h f) = J'.relIndex J • f := by
  have := Fintype.ofFinite (J ⧸ J'.subgroupOf J)
  ext g
  rw [levelFormsTrace_apply ρ Γ h _ Quotient.out (fun x ↦ QuotientGroup.out_eq' x) g]
  simp only [coe_levelFormsRes_apply, levelForms_apply_mul_right f, ← mul_apply_eq_comp,
    ← map_mul, ← op_mul, mul_inv_cancel, op_one, map_one, one_apply_eq_self, Finset.sum_const,
    Finset.card_univ, Submodule.coe_smul_of_tower, Pi.smul_apply, Subgroup.relIndex,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Level

end Representation
