/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Finiteness.Projective
public import TauCeti.Algebra.Module.MinimalProjectivePresentation.Basic

/-!
# The Auslander--Reiten transpose

Given a projective presentation `P₁ → P₀ → M`, applying `Hom_A(-, A)` reverses the first map.
The cokernel

`Hom_A(P₁, A) / range(Hom_A(P₀, A) → Hom_A(P₁, A))`

is the **Auslander--Reiten transpose** of the presentation.  It is naturally a left module over the
opposite ring `Aᵐᵒᵖ`: an element `op a` acts on a functional by multiplication by `a` on the right.
Mathlib already supplies this opposite-ring module structure on `Module.Dual A P` and the
precomposition map as `p.lcomp Aᵐᵒᵖ A`; this file forms its cokernel rather than rebuilding either.

The transpose is independent, up to linear equivalence, of the chosen minimal projective
presentation.  More precisely, an isomorphism of presentation diagrams induces an equivalence of
the two cokernels (`AuslanderReitenTranspose.linearEquiv`), characterized on representatives, and
the uniqueness theorem for minimal presentations then gives
`IsMinimalProjectivePresentation.nonempty_linearEquiv_auslanderReitenTranspose`.

The construction is additive in the presenting arrow: `AuslanderReitenTranspose.prodMapEquiv`
identifies the transpose of a direct sum with the product of the two transposes, while
`AuslanderReitenTranspose.compFstEquiv` identifies the transpose of an arrow enlarged by a zero
source summand with the product of its transpose and the dual of that summand.

The transpose is a construction on the *non-projective* modules: for a minimal projective
presentation `P₁ → P₀ → M` whose left-hand source `P₁` is finitely generated, it vanishes on a
projective `M` and on no other, which is
`IsMinimalProjectivePresentation.subsingleton_auslanderReitenTranspose_iff_projective`.

This supplies the transpose construction in sublayer 6C of the quiver-representations roadmap.
The remaining part of 6C develops its stable equivalence; sublayer 6D applies the duality
`D = Hom_k(-, k)` to construct the Auslander--Reiten translate `τ = D Tr`, in
`TauCeti/Algebra/Module/AuslanderReiten/Translate.lean`.  The scalar structure that duality
dualizes over — a base ring `k` of `A` acting on the transpose through `Aᵐᵒᵖ` — is supplied here,
next to the other module structures on the transpose.

## Main definitions

* `AuslanderReitenTranspose`: the cokernel of the dual of the first map in a projective
  presentation.
* `AuslanderReitenTranspose.lift`: the universal property of that cokernel, descending an
  opposite-linear map that kills the functionals factoring through `p₁`.
* `AuslanderReitenTranspose.linearEquiv`: the equivalence induced by an isomorphism of presentation
  diagrams.
* `AuslanderReitenTranspose.prodMapEquiv`: the transpose of a direct sum of arrows is the direct
  sum of their transposes.
* `AuslanderReitenTranspose.compFstEquiv`: a zero source summand contributes its dual to the
  transpose.

## Main results

* `AuslanderReitenTranspose.subsingleton_iff_exists_comp_eq_id`: for a finitely generated
  projective `P₁`, the transpose of `p₁` vanishes exactly when `p₁` is a split monomorphism.
* `IsMinimalProjectivePresentation.subsingleton_auslanderReitenTranspose_iff_projective`: for a
  minimal projective presentation with finitely generated left-hand source, **the transpose
  vanishes exactly on the projective modules**.  The forward direction is
  `IsMinimalProjectivePresentation.subsingleton_auslanderReitenTranspose_of_projective` and needs
  no finiteness; the converse is
  `IsMinimalProjectivePresentation.projective_of_subsingleton_auslanderReitenTranspose`, and asks
  the left-hand source of the presentation to be finitely generated, which it is over an Artin
  algebra once the presented module is.
* `IsMinimalProjectivePresentation.nonempty_linearEquiv_auslanderReitenTranspose`: the transpose
  does not depend on the chosen minimal presentation.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section IV.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Cambridge University Press (2006), Section IV.2.
-/

public section

namespace TauCeti

universe u v w v' w'

variable {A : Type u} [Ring A]

section Transpose

variable {P₀ : Type v} {P₁ : Type w} [AddCommMonoid P₀] [Module A P₀]
  [AddCommMonoid P₁] [Module A P₁]

/-- The **Auslander--Reiten transpose** attached to a projective presentation whose first map is
`p₁ : P₁ → P₀`.  It is the cokernel of the opposite-linear precomposition map
`Hom_A(P₀, A) → Hom_A(P₁, A)`.

Minimality is not needed to form the cokernel.  It is used by
`IsMinimalProjectivePresentation.nonempty_linearEquiv_auslanderReitenTranspose` to show that the
result is independent, up to equivalence, of the chosen presentation of a module. -/
def AuslanderReitenTranspose (p₁ : P₁ →ₗ[A] P₀) : Type _ :=
  Module.Dual A P₁ ⧸ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)

namespace AuslanderReitenTranspose

variable (p₁ : P₁ →ₗ[A] P₀)

instance : AddCommGroup (AuslanderReitenTranspose p₁) :=
  inferInstanceAs (AddCommGroup (Module.Dual A P₁ ⧸ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)))

instance : Module Aᵐᵒᵖ (AuslanderReitenTranspose p₁) :=
  inferInstanceAs (Module Aᵐᵒᵖ (Module.Dual A P₁ ⧸ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)))

section Scalars

variable (k : Type*) [CommSemiring k] [Algebra k A]

/-- A base ring `k` of `A` acts on the transpose, through the algebra map into `Aᵐᵒᵖ`.  This is the
scalar structure the Auslander--Reiten translate dualizes over. -/
instance : Module k (AuslanderReitenTranspose p₁) :=
  inferInstanceAs (Module k (Module.Dual A P₁ ⧸ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)))

instance : IsScalarTower k Aᵐᵒᵖ (AuslanderReitenTranspose p₁) :=
  inferInstanceAs (IsScalarTower k Aᵐᵒᵖ (Module.Dual A P₁ ⧸ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)))

instance : SMulCommClass Aᵐᵒᵖ k (AuslanderReitenTranspose p₁) :=
  inferInstanceAs (SMulCommClass Aᵐᵒᵖ k (Module.Dual A P₁ ⧸ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)))

/-- A scalar of `k`, viewed in `Aᵐᵒᵖ` through the algebra map, acts on the transpose as it does
through the `k`-action itself. -/
@[simp]
theorem op_algebraMap_smul (c : k) (x : AuslanderReitenTranspose p₁) :
    MulOpposite.op (algebraMap k A c) • x = c • x := by
  rw [← MulOpposite.algebraMap_apply, algebraMap_smul]

end Scalars

/-- The quotient map from the dual of the first projective onto its Auslander--Reiten transpose. -/
def mk : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p₁ :=
  (LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)).mkQ

/-- A functional represents zero in the transpose exactly when it factors through the first map of
the presentation. -/
@[simp]
theorem mk_eq_zero_iff (φ : Module.Dual A P₁) :
    mk p₁ φ = 0 ↔ φ ∈ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A) :=
  Submodule.Quotient.mk_eq_zero _

/-- The quotient map onto the transpose kills exactly the functionals factoring through the first
map of the presentation. -/
@[simp]
theorem ker_mk : LinearMap.ker (mk p₁) = LinearMap.range (p₁.lcomp Aᵐᵒᵖ A) := by
  ext φ
  simp [LinearMap.mem_ker]

/-- A functional precomposed with the first map of the presentation vanishes in its cokernel. -/
@[simp]
theorem mk_lcomp (φ : Module.Dual A P₀) :
    mk p₁ (p₁.lcomp Aᵐᵒᵖ A φ) = 0 := by
  rw [mk_eq_zero_iff]
  exact LinearMap.mem_range_self _ φ

/-- Every element of the transpose is represented by a functional on `P₁`. -/
theorem mk_surjective : Function.Surjective (mk p₁) :=
  Submodule.mkQ_surjective _

/-- Two functionals represent the same element of the transpose exactly when their difference
factors through the first map of the presentation. -/
@[simp]
theorem mk_eq_mk_iff (φ ψ : Module.Dual A P₁) :
    mk p₁ φ = mk p₁ ψ ↔ φ - ψ ∈ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A) :=
  Submodule.Quotient.eq _

/-- To prove a property of every element of the transpose it suffices to prove it of the classes
of functionals on `P₁`. -/
@[elab_as_elim]
theorem induction_on {motive : AuslanderReitenTranspose p₁ → Prop}
    (x : AuslanderReitenTranspose p₁) (h : ∀ φ : Module.Dual A P₁, motive (mk p₁ φ)) :
    motive x :=
  Submodule.Quotient.induction_on _ x h

section QuotientEquiv

variable {S N : Type*} [Ring S] [AddCommGroup N] [Module S N]
  {σ : Aᵐᵒᵖ →+* S} {σ' : S →+* Aᵐᵒᵖ}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-- A semilinear equivalence carrying the range of precomposition onto `Q` identifies the
transpose with the quotient by `Q`. -/
def quotientEquiv (Q : Submodule S N) (e : Module.Dual A P₁ ≃ₛₗ[σ] N)
    (he : (LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)).map e.toLinearMap = Q) :
    AuslanderReitenTranspose p₁ ≃ₛₗ[σ] N ⧸ Q :=
  Submodule.Quotient.equiv _ Q e he

/-- Quotient transport applies the semilinear equivalence to a functional representative. -/
@[simp]
theorem quotientEquiv_mk (Q : Submodule S N) (e : Module.Dual A P₁ ≃ₛₗ[σ] N)
    (he : (LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)).map e.toLinearMap = Q)
    (φ : Module.Dual A P₁) :
    quotientEquiv p₁ Q e he (mk p₁ φ) = Submodule.Quotient.mk (e φ) := by
  -- The transpose, `mk`, and `quotientEquiv` have unexposed bodies. Present their quotient
  -- form locally so that the public quotient application lemmas can apply.
  with_unfolding_all
    change Submodule.Quotient.equiv _ Q e he (Submodule.Quotient.mk φ) = _
    rw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe]

/-- Inverse quotient transport applies the inverse equivalence to a quotient representative. -/
@[simp]
theorem quotientEquiv_symm_mk (Q : Submodule S N) (e : Module.Dual A P₁ ≃ₛₗ[σ] N)
    (he : (LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)).map e.toLinearMap = Q) (n : N) :
    (quotientEquiv p₁ Q e he).symm (Submodule.Quotient.mk n) = mk p₁ (e.symm n) := by
  apply (quotientEquiv p₁ Q e he).injective
  simp

end QuotientEquiv

section Lift

variable {N : Type*} [AddCommGroup N] [Module Aᵐᵒᵖ N]

/-- The universal property of the transpose: an opposite-linear map out of `Hom_A(P₁, A)` that
kills every functional factoring through `p₁` descends to the cokernel. -/
def lift (f : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] N)
    (hf : ∀ φ : Module.Dual A P₀, f (p₁.lcomp Aᵐᵒᵖ A φ) = 0) :
    AuslanderReitenTranspose p₁ →ₗ[Aᵐᵒᵖ] N :=
  Submodule.liftQ _ f <| by
    rintro _ ⟨φ, rfl⟩
    exact hf φ

@[simp]
theorem lift_mk (f : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] N)
    (hf : ∀ φ : Module.Dual A P₀, f (p₁.lcomp Aᵐᵒᵖ A φ) = 0) (φ : Module.Dual A P₁) :
    lift p₁ f hf (mk p₁ φ) = f φ :=
  Submodule.liftQ_apply _ f φ

/-- `AuslanderReitenTranspose.lift` factors the given map through the quotient map. -/
@[simp]
theorem lift_comp_mk (f : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] N)
    (hf : ∀ φ : Module.Dual A P₀, f (p₁.lcomp Aᵐᵒᵖ A φ) = 0) :
    (lift p₁ f hf).comp (mk p₁) = f :=
  LinearMap.ext fun φ => lift_mk p₁ f hf φ

/-- Opposite-linear maps out of the transpose are determined by their values on representatives. -/
@[ext]
theorem hom_ext {f g : AuslanderReitenTranspose p₁ →ₗ[Aᵐᵒᵖ] N}
    (h : ∀ φ : Module.Dual A P₁, f (mk p₁ φ) = g (mk p₁ φ)) : f = g :=
  LinearMap.ext fun x => induction_on p₁ x h

/-- `AuslanderReitenTranspose.lift` is the unique descent of `f` to the transpose. -/
theorem eq_lift (f : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] N)
    (hf : ∀ φ : Module.Dual A P₀, f (p₁.lcomp Aᵐᵒᵖ A φ) = 0)
    (g : AuslanderReitenTranspose p₁ →ₗ[Aᵐᵒᵖ] N)
    (hg : ∀ φ : Module.Dual A P₁, g (mk p₁ φ) = f φ) :
    g = lift p₁ f hf :=
  hom_ext p₁ fun φ => by rw [hg, lift_mk]

end Lift

section Additivity

open LinearMap

variable {A₁ A₂ E₁ E₂ : Type*} [AddCommMonoid A₁] [Module A A₁] [AddCommMonoid A₂] [Module A A₂]
  [AddCommMonoid E₁] [Module A E₁] [AddCommMonoid E₂] [Module A E₂]
  (u : A₁ →ₗ[A] E₁) (w : A₂ →ₗ[A] E₂)

/-- **The transpose is additive.** The transpose of the direct sum `u ⊕ w` of two arrows is the
direct sum of their transposes. On representatives it restricts a functional on `A₁ × A₂` to the
two summands. -/
def prodMapEquiv :
    AuslanderReitenTranspose (u.prodMap w) ≃ₗ[Aᵐᵒᵖ]
      AuslanderReitenTranspose u × AuslanderReitenTranspose w :=
  LinearEquiv.ofLinearMap
    (lift (u.prodMap w)
      ((mk u ∘ₗ (inl A A₁ A₂).lcomp Aᵐᵒᵖ A).prod (mk w ∘ₗ (inr A A₁ A₂).lcomp Aᵐᵒᵖ A))
      fun φ => by
        refine Prod.ext ((mk_eq_zero_iff _ _).mpr ⟨φ ∘ₗ inl A E₁ E₂, ?_⟩)
          ((mk_eq_zero_iff _ _).mpr ⟨φ ∘ₗ inr A E₁ E₂, ?_⟩) <;> ext <;> simp)
    ((lift u (mk (u.prodMap w) ∘ₗ (fst A A₁ A₂).lcomp Aᵐᵒᵖ A) fun φ =>
        (mk_eq_zero_iff _ _).mpr ⟨φ ∘ₗ fst A E₁ E₂, by ext <;> simp⟩).coprod
      (lift w (mk (u.prodMap w) ∘ₗ (snd A A₁ A₂).lcomp Aᵐᵒᵖ A) fun φ =>
        (mk_eq_zero_iff _ _).mpr ⟨φ ∘ₗ snd A E₁ E₂, by ext <;> simp⟩))
    (by
      apply prod_ext <;> ext φ <;> simp [lcomp_apply', comp_assoc])
    (by
      ext φ
      simp only [comp_apply, lift_mk, coprod_apply, prod_apply, Function.prod, lcomp_apply',
        id_apply]
      rw [← map_add]
      congr 1
      ext <;> simp [← Prod.zero_eq_mk])

/-- The equivalence `prodMapEquiv` restricts a representative to the two summands. -/
@[simp]
theorem prodMapEquiv_mk (φ : Module.Dual A (A₁ × A₂)) :
    prodMapEquiv u w (mk (u.prodMap w) φ) =
      (mk u (φ ∘ₗ inl A A₁ A₂), mk w (φ ∘ₗ inr A A₁ A₂)) := by
  simp [prodMapEquiv, lcomp_apply']

/-- The inverse of `prodMapEquiv` combines representatives using the canonical functional on the
product. -/
@[simp]
theorem prodMapEquiv_symm_mk (φ : Module.Dual A A₁) (ψ : Module.Dual A A₂) :
    (prodMapEquiv u w).symm (mk u φ, mk w ψ) = mk (u.prodMap w) (φ.coprod ψ) := by
  apply (prodMapEquiv u w).injective
  simp

variable (C : Type*) [AddCommMonoid C] [Module A C]

/-- **A zero summand contributes its dual.** Enlarging the source of `u : A₁ → E₁` by a summand
`C` on which the arrow vanishes adds `Hom_A(C, A)` to the transpose. On representatives it
restricts a functional on `A₁ × C` to the two summands. -/
def compFstEquiv :
    AuslanderReitenTranspose (u ∘ₗ fst A A₁ C) ≃ₗ[Aᵐᵒᵖ]
      AuslanderReitenTranspose u × Module.Dual A C :=
  LinearEquiv.ofLinearMap
    (lift (u ∘ₗ fst A A₁ C)
      ((mk u ∘ₗ (inl A A₁ C).lcomp Aᵐᵒᵖ A).prod ((inr A A₁ C).lcomp Aᵐᵒᵖ A))
      fun φ => by
        refine Prod.ext ((mk_eq_zero_iff _ _).mpr ⟨φ, ?_⟩) ?_ <;> ext <;> simp)
    ((lift u (mk (u ∘ₗ fst A A₁ C) ∘ₗ (fst A A₁ C).lcomp Aᵐᵒᵖ A) fun φ =>
        (mk_eq_zero_iff _ _).mpr ⟨φ, by ext <;> simp⟩).coprod
      (mk (u ∘ₗ fst A A₁ C) ∘ₗ (snd A A₁ C).lcomp Aᵐᵒᵖ A))
    (by
      apply prod_ext <;> ext φ <;> simp [lcomp_apply', comp_assoc])
    (by
      ext φ
      simp only [comp_apply, lift_mk, coprod_apply, prod_apply, Function.prod, lcomp_apply',
        id_apply]
      rw [← map_add]
      congr 1
      ext <;> simp [← Prod.zero_eq_mk])

/-- The equivalence `compFstEquiv` restricts a representative to the two summands. -/
@[simp]
theorem compFstEquiv_mk (φ : Module.Dual A (A₁ × C)) :
    compFstEquiv u C (mk (u ∘ₗ fst A A₁ C) φ) = (mk u (φ ∘ₗ inl A A₁ C), φ ∘ₗ inr A A₁ C) := by
  simp [compFstEquiv, lcomp_apply']

/-- The inverse of `compFstEquiv` combines representatives using the canonical functional on the
product. -/
@[simp]
theorem compFstEquiv_symm_mk (φ : Module.Dual A A₁) (ψ : Module.Dual A C) :
    (compFstEquiv u C).symm (mk u φ, ψ) = mk (u ∘ₗ fst A A₁ C) (φ.coprod ψ) := by
  apply (compFstEquiv u C).injective
  simp

end Additivity

section Split

/-- **A split presenting map has vanishing transpose.**  If `p₁` admits a retraction, its
Auslander--Reiten transpose is a subsingleton.

No finiteness or projectivity is needed for this direction;
`TauCeti.AuslanderReitenTranspose.exists_comp_eq_id_of_subsingleton` is the converse, and it needs
both. -/
theorem subsingleton_of_comp_eq_id {r : P₀ →ₗ[A] P₁} (hr : r ∘ₗ p₁ = LinearMap.id) :
    Subsingleton (AuslanderReitenTranspose p₁) := by
  have hzero : ∀ x : AuslanderReitenTranspose p₁, x = 0 := by
    intro x
    induction x using induction_on p₁ with
    | _ φ =>
      rw [mk_eq_zero_iff]
      refine ⟨φ ∘ₗ r, LinearMap.ext fun y => ?_⟩
      simp only [LinearMap.lcomp_apply, LinearMap.comp_apply]
      exact congrArg φ (by simpa using LinearMap.congr_fun hr y)
  exact ⟨fun x y => by rw [hzero x, hzero y]⟩

/-- **A vanishing transpose splits the presenting map.**  If `P₁` is a finitely generated
projective module and the transpose of `p₁ : P₁ → P₀` vanishes, then `p₁` admits a retraction.

Both hypotheses on `P₁` are needed, and they are needed together: they supply a *finite* dual
basis of `P₁`, and only finitely many functionals may be assembled into a single map `P₀ → P₁`. -/
theorem exists_comp_eq_id_of_subsingleton [Module.Finite A P₁] [Module.Projective A P₁]
    (h : Subsingleton (AuslanderReitenTranspose p₁)) :
    ∃ r : P₀ →ₗ[A] P₁, r ∘ₗ p₁ = LinearMap.id := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P₁
  have hcoord : ∀ i : Fin n, ∃ ψ : Module.Dual A P₀,
      p₁.lcomp Aᵐᵒᵖ A ψ = (LinearMap.proj i : (Fin n → A) →ₗ[A] A) ∘ₗ g :=
    fun i => LinearMap.mem_range.mp ((mk_eq_zero_iff p₁ _).mp (Subsingleton.elim _ 0))
  choose ψ hψ using hcoord
  refine ⟨f ∘ₗ LinearMap.pi ψ, LinearMap.ext fun x => ?_⟩
  have hx : LinearMap.pi ψ (p₁ x) = g x := by
    funext i
    simpa using LinearMap.congr_fun (hψ i) x
  simpa [hx] using LinearMap.congr_fun hfg x

/-- **The transpose vanishes exactly when the presenting map splits**, for a finitely generated
projective `P₁`. -/
theorem subsingleton_iff_exists_comp_eq_id [Module.Finite A P₁] [Module.Projective A P₁] :
    Subsingleton (AuslanderReitenTranspose p₁) ↔ ∃ r : P₀ →ₗ[A] P₁, r ∘ₗ p₁ = LinearMap.id :=
  ⟨exists_comp_eq_id_of_subsingleton p₁, fun ⟨_, hr⟩ => subsingleton_of_comp_eq_id p₁ hr⟩

end Split

variable {p₁}

section Equivalence

variable {Q₀ : Type v'} {Q₁ : Type w'} [AddCommMonoid Q₀] [Module A Q₀]
  [AddCommMonoid Q₁] [Module A Q₁]

private theorem map_range_lcomp_eq {q₁ : Q₁ →ₗ[A] Q₀} (e₀ : P₀ ≃ₗ[A] Q₀)
    (e₁ : P₁ ≃ₗ[A] Q₁)
    (hsquare : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap) :
    Submodule.map (e₁.congrLeft A Aᵐᵒᵖ : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] Module.Dual A Q₁)
        (LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)) =
      LinearMap.range (q₁.lcomp Aᵐᵒᵖ A) := by
  rw [← LinearMap.range_comp]
  have hcomp :
      (e₁.congrLeft A Aᵐᵒᵖ).toLinearMap.comp (p₁.lcomp Aᵐᵒᵖ A) =
        (q₁.lcomp Aᵐᵒᵖ A).comp (e₀.congrLeft A Aᵐᵒᵖ).toLinearMap := by
    ext φ x
    simp only [LinearMap.comp_apply, LinearMap.lcomp_apply]
    apply congrArg φ
    simpa using congrArg e₀.symm (LinearMap.congr_fun hsquare (e₁.symm x))
  rw [hcomp, LinearEquiv.range_comp]

/-- An isomorphism of the first square of two projective presentations induces an equivalence of
their Auslander--Reiten transposes.  On representatives it sends `φ : Hom_A(P₁, A)` to
`φ ∘ e₁⁻¹ : Hom_A(Q₁, A)`.

The equivalence depends only on the two presentation isomorphisms and their commutative square; the
maps from `P₀` and `Q₀` to the presented module do not enter the cokernel. -/
def linearEquiv {q₁ : Q₁ →ₗ[A] Q₀} (e₀ : P₀ ≃ₗ[A] Q₀)
    (e₁ : P₁ ≃ₗ[A] Q₁)
    (hsquare : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap) :
    AuslanderReitenTranspose p₁ ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose q₁ :=
  quotientEquiv p₁ _ (e₁.congrLeft A Aᵐᵒᵖ) (map_range_lcomp_eq e₀ e₁ hsquare)

/-- The presentation equivalence on transposes, evaluated on a functional representative. -/
@[simp]
theorem linearEquiv_mk {q₁ : Q₁ →ₗ[A] Q₀} (e₀ : P₀ ≃ₗ[A] Q₀)
    (e₁ : P₁ ≃ₗ[A] Q₁)
    (hsquare : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap)
    (φ : Module.Dual A P₁) :
    linearEquiv e₀ e₁ hsquare (mk p₁ φ) =
      mk q₁ (e₁.symm.toLinearMap.lcomp Aᵐᵒᵖ A φ) := by
  have hrep : (e₁.congrLeft A Aᵐᵒᵖ : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] Module.Dual A Q₁) φ =
      e₁.symm.toLinearMap.lcomp Aᵐᵒᵖ A φ := by
    ext x
    simp [LinearMap.lcomp_apply]
  exact (quotientEquiv_mk p₁ _ (e₁.congrLeft A Aᵐᵒᵖ)
    (map_range_lcomp_eq e₀ e₁ hsquare) φ).trans (congrArg (mk q₁) hrep)

/-- Transport along the identity presentation equivalences is the identity. -/
@[simp]
theorem linearEquiv_refl :
    linearEquiv (LinearEquiv.refl A P₀) (LinearEquiv.refl A P₁) (by simp) =
      LinearEquiv.refl Aᵐᵒᵖ (AuslanderReitenTranspose p₁) := by
  apply LinearEquiv.ext
  intro x
  induction x using induction_on p₁ with
  | _ φ =>
    rw [linearEquiv_mk]
    apply congrArg (mk p₁)
    ext y
    simp only [LinearMap.lcomp_apply, LinearEquiv.refl_symm, LinearEquiv.refl_toLinearMap,
      LinearMap.id_apply]

/-- Transport along a composite of presentation equivalences is the composite transport. -/
@[simp]
theorem linearEquiv_trans {q₁ : Q₁ →ₗ[A] Q₀}
    {R₀ R₁ : Type*} [AddCommMonoid R₀] [Module A R₀] [AddCommMonoid R₁] [Module A R₁]
    {r₁ : R₁ →ₗ[A] R₀} (e₀ : P₀ ≃ₗ[A] Q₀) (e₁ : P₁ ≃ₗ[A] Q₁)
    (f₀ : Q₀ ≃ₗ[A] R₀) (f₁ : Q₁ ≃ₗ[A] R₁)
    (he : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap)
    (hf : f₀.toLinearMap ∘ₗ q₁ = r₁ ∘ₗ f₁.toLinearMap) :
    (linearEquiv e₀ e₁ he).trans (linearEquiv f₀ f₁ hf) =
      linearEquiv (e₀.trans f₀) (e₁.trans f₁)
        (by
          ext x
          have h₀ := LinearMap.congr_fun he x
          have h₁ := LinearMap.congr_fun hf (e₁ x)
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h₀ h₁ ⊢
          rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h₀, h₁]) := by
  apply LinearEquiv.ext
  intro x
  induction x using induction_on p₁ with
  | _ φ =>
    rw [LinearEquiv.trans_apply, linearEquiv_mk, linearEquiv_mk, linearEquiv_mk]
    apply congrArg (mk r₁)
    ext y
    simp only [LinearMap.lcomp_apply, LinearEquiv.trans_symm, LinearEquiv.coe_trans,
      LinearMap.comp_apply]

/-- The inverse of transport is transport along the inverse presentation equivalences. -/
@[simp]
theorem linearEquiv_symm {q₁ : Q₁ →ₗ[A] Q₀} (e₀ : P₀ ≃ₗ[A] Q₀)
    (e₁ : P₁ ≃ₗ[A] Q₁)
    (hsquare : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap) :
    (linearEquiv e₀ e₁ hsquare).symm =
      linearEquiv e₀.symm e₁.symm
        (by
          ext x
          have h := LinearMap.congr_fun hsquare (e₁.symm x)
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
            LinearEquiv.apply_symm_apply] at h ⊢
          rw [← h, LinearEquiv.symm_apply_apply]) := by
  apply LinearEquiv.ext
  intro x
  induction x using induction_on q₁ with
  | _ φ =>
    apply (linearEquiv e₀ e₁ hsquare).injective
    rw [LinearEquiv.apply_symm_apply, linearEquiv_mk, linearEquiv_mk]
    apply congrArg (mk q₁)
    ext y
    simp only [LinearMap.lcomp_apply, LinearEquiv.symm_symm]
    exact congrArg φ (e₁.apply_symm_apply y).symm

end Equivalence

end AuslanderReitenTranspose

end Transpose

namespace IsMinimalProjectivePresentation

variable {M : Type*} [AddCommGroup M] [Module A M]
variable {P₀ : Type v} [AddCommGroup P₀] [Module A P₀]

section Projective

variable {P₁ : Type w} [AddCommMonoid P₁] [Module A P₁]
variable {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}

/-- The Auslander--Reiten transpose of a projective module is zero, represented here by the
stronger typeclass-friendly statement that its underlying quotient is a subsingleton. -/
theorem subsingleton_auslanderReitenTranspose_of_projective
    [Module.Projective A M] (h : IsMinimalProjectivePresentation p₁ p₀) :
    Subsingleton (AuslanderReitenTranspose p₁) := by
  let _ : Subsingleton P₁ := h.subsingleton_of_projective
  constructor
  intro x y
  induction x using AuslanderReitenTranspose.induction_on p₁ with
  | _ φ =>
    induction y using AuslanderReitenTranspose.induction_on p₁ with
    | _ ψ => exact congrArg (AuslanderReitenTranspose.mk p₁) (Subsingleton.elim φ ψ)

end Projective

section Vanishing

variable {P₁ : Type w} [AddCommGroup P₁] [Module A P₁]
variable {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}

/-- **A module with vanishing Auslander--Reiten transpose is projective**, the converse of
`TauCeti.IsMinimalProjectivePresentation.subsingleton_auslanderReitenTranspose_of_projective`.

Finite generation of `P₁` is a genuine hypothesis rather than a convenience: it is what makes the
dual basis splitting `p₁` finite.  It is automatic for a *finitely generated* `M` over an Artin
algebra, where such an `M` has a minimal projective presentation by finitely generated
projectives. -/
theorem projective_of_subsingleton_auslanderReitenTranspose [Module.Finite A P₁]
    (h : IsMinimalProjectivePresentation p₁ p₀)
    (hTr : Subsingleton (AuslanderReitenTranspose p₁)) : Module.Projective A M := by
  let _ : Module.Projective A P₁ := h.projective
  obtain ⟨r, hr⟩ := AuslanderReitenTranspose.exists_comp_eq_id_of_subsingleton p₁ hTr
  have hid : ∀ x : P₁, r (p₁ x) = x := fun x => by simpa using LinearMap.congr_fun hr x
  -- The retraction splits `P₀` as `range p₁ ⊔ ker r`, and `range p₁` is the superfluous syzygy.
  have hsup : LinearMap.ker p₀ ⊔ LinearMap.ker r = ⊤ := by
    rw [← h.range_eq_ker, eq_top_iff]
    rintro y -
    have hy : y = p₁ (r y) + (y - p₁ (r y)) := by abel
    rw [hy]
    refine Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_ker.mpr ?_)
    rw [map_sub, hid (r y), sub_self]
  have hker : LinearMap.ker r = ⊤ :=
    h.isProjectiveCover.isSuperfluous_ker.eq_top_of_sup_eq_top hsup
  -- A retraction that kills everything forces its section's source to vanish.
  have hzero : ∀ x : P₁, x = 0 := fun x => by
    rw [← hid x]
    exact LinearMap.mem_ker.mp (by rw [hker]; trivial)
  have hp₁ : p₁ = 0 := by
    ext x
    rw [hzero x]
    simp
  have hkerp₀ : LinearMap.ker p₀ = ⊥ := by
    rw [← h.range_eq_ker, hp₁, LinearMap.range_zero]
  let _ : Module.Projective A P₀ := h.isProjectiveCover.projective
  exact Module.Projective.of_equiv'
    (LinearEquiv.ofBijective p₀ ⟨LinearMap.ker_eq_bot.mp hkerp₀, h.surjective⟩)

/-- **The Auslander--Reiten transpose vanishes exactly on the projective modules.**  This is what
makes `Tr`, and with it the translate `τ = D Tr`, a construction on *non-projective* modules: it
carries no information about a projective one and detects every other. -/
theorem subsingleton_auslanderReitenTranspose_iff_projective [Module.Finite A P₁]
    (h : IsMinimalProjectivePresentation p₁ p₀) :
    Subsingleton (AuslanderReitenTranspose p₁) ↔ Module.Projective A M :=
  ⟨h.projective_of_subsingleton_auslanderReitenTranspose,
    fun _ => h.subsingleton_auslanderReitenTranspose_of_projective⟩

end Vanishing

section Comparison

variable {P₁ : Type w} [AddCommGroup P₁] [Module A P₁]
variable {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}
variable {Q₀ : Type v'} {Q₁ : Type w'} [AddCommGroup Q₀] [Module A Q₀]
  [AddCommGroup Q₁] [Module A Q₁]
variable {q₁ : Q₁ →ₗ[A] Q₀} {q₀ : Q₀ →ₗ[A] M}

/-- The Auslander--Reiten transpose is independent, up to opposite-linear equivalence, of the
chosen minimal projective presentation of a module. -/
theorem nonempty_linearEquiv_auslanderReitenTranspose
    (h : IsMinimalProjectivePresentation p₁ p₀)
    (h' : IsMinimalProjectivePresentation q₁ q₀) :
    Nonempty (AuslanderReitenTranspose p₁ ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose q₁) := by
  obtain ⟨e₀, e₁, -, hsquare⟩ := h.exists_linearEquiv h'
  exact ⟨AuslanderReitenTranspose.linearEquiv e₀ e₁ hsquare⟩

end Comparison

end IsMinimalProjectivePresentation

end TauCeti
