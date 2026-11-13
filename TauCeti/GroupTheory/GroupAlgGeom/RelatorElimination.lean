/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.Automorphism

/-!
# Eliminating a relator which is a basis element

Let `S` be a system of equations over `G` in the variables `X` and `s ∈ G[X]` a further relator.
Suppose that after a coefficient-fixing automorphism `τ` of `G[X]` the relator `s` becomes `u x v`
for a variable `x` occurring neither in the words `u`, `v` nor in the images of the relators of
`S`; that is, `s` belongs to a free basis of `G[X]` over `G` whose other members generate, together
with `G`, a free factor containing `S`. Then adding `s` to `S` kills a free factor: the group
`G_S = G[X] ⧸ ncl(S)` presented by `S` is the free product of the group presented by `S` and `s`
with an infinite cyclic group `⟨z⟩`, `z` corresponding to `s`, and sending `z` to `1` gives back
the quotient map (`TauCeti.GroupAlgGeom.SystemGroup.exists_bijective_of_normalClosure_eq_insert`).

This is the Tietze transformation behind the elimination of a base of a generalised equation
(Kharlampovich–Myasnikov, D4), where the basic equation of an eliminable base becomes, after a
change of variables, a basis element of the ambient free group.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.2, D4.
* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Chapter II, §2 (Tietze
  transformations).
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod Subgroup

variable {G X : Type*} [Group G] [DecidableEq X]

namespace SystemGroup

section Elimination

variable (τ : MulAut (GX G X)) (x : X)

/-- The class in `G_S` of the image of a word under `τ⁻¹`. -/
private abbrev symmMk (S : Set (GX G X)) : GX G X →* SystemGroup G S :=
  (QuotientGroup.mk' _).comp τ.symm.toMonoidHom

/-- The class in `G_T`, included in `G_T ∗ ⟨z⟩`, of the image of a word under `τ⁻¹`. -/
private abbrev inlSymmMk (T : Set (GX G X)) : GX G X →* GX (SystemGroup G T) Unit :=
  (inl : SystemGroup G T →* GX (SystemGroup G T) Unit).comp (symmMk τ T)

/-- The homomorphism `G[X] → G_T ∗ ⟨z⟩` sending `x` to `z` and every other variable `y` to
the class of `τ⁻¹ y`. -/
private def toCoprod (T : Set (GX G X)) : GX G X →* GX (SystemGroup G T) Unit :=
  eval ((inlSymmMk τ T).comp inl) (Function.update (fun y => inlSymmMk τ T (inr (FreeGroup.of y)))
    x (inr (FreeGroup.of ())))

/-- The homomorphism `G[X] → G_S` sending `x` to `1` and every other variable `y` to the class of
`τ⁻¹ y`. -/
private def retract (S : Set (GX G X)) : GX G X →* SystemGroup G S :=
  eval ((symmMk τ S).comp inl) (Function.update (fun y => symmMk τ S (inr (FreeGroup.of y))) x 1)

variable {τ x}

private theorem toCoprod_of_mem_avoiding (T : Set (GX G X)) {a : GX G X} (ha : a ∈ GX.avoiding x) :
    toCoprod τ x T a = inl (τ.symm a : SystemGroup G T) := by
  rw [toCoprod, GX.eval_update_of_mem_avoiding _ ha, ← eq_eval]
  rfl

private theorem toCoprod_inr_self (T : Set (GX G X)) :
    toCoprod τ x T (inr (FreeGroup.of x)) = inr (FreeGroup.of ()) := by
  simp [toCoprod]

private theorem retract_of_mem_avoiding (S : Set (GX G X)) {a : GX G X} (ha : a ∈ GX.avoiding x) :
    retract τ x S a = (τ.symm a : SystemGroup G S) := by
  rw [retract, GX.eval_update_of_mem_avoiding _ ha, ← eq_eval]
  rfl

private theorem retract_inr_self (S : Set (GX G X)) : retract τ x S (inr (FreeGroup.of x)) = 1 := by
  simp [retract]

variable {S T : Set (GX G X)} {s : GX G X}

/-- A homomorphism `G_T ∗ ⟨z⟩ → G_S` which is `retract ∘ τ` on `G_T` and sends `z` to `s`, composed
with `toCoprod`, is the class map of `τ⁻¹`. -/
private theorem lift_comp_toCoprod (hσx : τ.symm (inr (FreeGroup.of x)) = s)
    {φ : SystemGroup G T →* SystemGroup G S} (hφ : ∀ w : GX G X, φ w = retract τ x S (τ w)) :
    (lift φ (FreeGroup.lift fun _ => (s : SystemGroup G S))).comp (toCoprod τ x T) =
      symmMk τ S :=
  GX.hom_ext_of_avoiding (x := x)
    (fun a ha => by simp [hφ, toCoprod_of_mem_avoiding T ha, retract_of_mem_avoiding S ha])
    (by simp [toCoprod_inr_self, hσx])

/-- A homomorphism `G_S → G_T ∗ ⟨z⟩` which is `toCoprod ∘ τ`, composed with `retract`, is
the class map of `τ⁻¹` into `G_T`, provided `s` is trivial in `G_T`. -/
private theorem comp_retract (hσx : τ.symm (inr (FreeGroup.of x)) = s)
    (hsT : (s : SystemGroup G T) = 1) {ψ : SystemGroup G S →* GX (SystemGroup G T) Unit}
    (hψ : ∀ w : GX G X, ψ w = toCoprod τ x T (τ w)) : ψ.comp (retract τ x S) = inlSymmMk τ T :=
  GX.hom_ext_of_avoiding (x := x)
    (fun a ha => by simp [hψ, toCoprod_of_mem_avoiding T ha, retract_of_mem_avoiding S ha])
    (by simp [retract_inr_self, hσx, hsT])

/-- Sending `z` to `1` after `toCoprod` gives the class map of `τ⁻¹`, provided `s` is trivial in
`G_T`. -/
private theorem eval_comp_toCoprod (hσx : τ.symm (inr (FreeGroup.of x)) = s)
    (hsT : (s : SystemGroup G T) = 1) :
    (eval (MonoidHom.id (SystemGroup G T)) fun _ => 1).comp (toCoprod τ x T) = symmMk τ T :=
  GX.hom_ext_of_avoiding (x := x) (fun a ha => by simp [toCoprod_of_mem_avoiding T ha])
    (by simp [toCoprod_inr_self, hσx, hsT])

/-- The case `τ s = x` of `exists_bijective_of_normalClosure_eq_insert`. -/
private theorem exists_bijective_of_apply_eq (hτ : ∀ g, τ (inl g) = inl g)
    (hs : τ s = inr (FreeGroup.of x)) (hS : ∀ t ∈ S, τ t ∈ GX.avoiding x)
    (hT : normalClosure T = normalClosure (insert s S)) :
    ∃ e : GHom (coeff S) ((inl : SystemGroup G T →* GX (SystemGroup G T) Unit).comp (coeff T)),
      Function.Bijective e ∧ (∀ w : GX G X,
        eval (MonoidHom.id (SystemGroup G T)) (fun _ => 1) (e (w : SystemGroup G S)) =
          (w : SystemGroup G T)) ∧ e (s : SystemGroup G S) = inr (FreeGroup.of ()) := by
  have hσx : τ.symm (inr (FreeGroup.of x)) = s := τ.symm_apply_eq.2 hs.symm
  have hT' {t} (ht : t ∈ insert s S) : (t : SystemGroup G T) = 1 :=
    (QuotientGroup.eq_one_iff t).2 (hT ▸ subset_normalClosure ht)
  -- `e : G_S → G_T ∗ ⟨z⟩` is induced by `toCoprod ∘ τ`, and its inverse `f` by `retract ∘ τ` on
  -- `G_T` and `z ↦ s`.
  let e : SystemGroup G S →* GX (SystemGroup G T) Unit :=
    QuotientGroup.lift _ ((toCoprod τ x T).comp τ.toMonoidHom) <| normalClosure_le_normal
      fun t ht => by
        rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          toCoprod_of_mem_avoiding T (hS t ht)]
        simp [hT' (Set.mem_insert_of_mem s ht)]
  let f₁ : SystemGroup G T →* SystemGroup G S :=
    QuotientGroup.lift _ ((retract τ x S).comp τ.toMonoidHom) <| hT ▸ normalClosure_le_normal (by
      rintro t (rfl | ht) <;>
        rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      · rw [hs, retract_inr_self]
      · rw [retract_of_mem_avoiding S (hS t ht)]
        simpa using (QuotientGroup.eq_one_iff _).2 (subset_normalClosure ht))
  let f : GX (SystemGroup G T) Unit →* SystemGroup G S :=
    lift f₁ (FreeGroup.lift fun _ => (s : SystemGroup G S))
  have hfe := lift_comp_toCoprod hσx (φ := f₁) fun w => QuotientGroup.lift_mk _ _ w
  have hef := comp_retract hσx (hT' (Set.mem_insert s S)) (ψ := e) fun w =>
    QuotientGroup.lift_mk _ _ w
  let E : SystemGroup G S ≃* GX (SystemGroup G T) Unit := e.toMulEquiv f
    (QuotientGroup.monoidHom_ext _ <| MonoidHom.ext fun w => by
      simpa [e, f] using DFunLike.congr_fun hfe (τ w))
    (hom_ext (QuotientGroup.monoidHom_ext _ <| MonoidHom.ext fun w => by
        simpa [f, f₁] using DFunLike.congr_fun hef (τ w))
      (FreeGroup.ext_hom _ _ fun _ => by simp [f, e, hs, toCoprod_inr_self]))
  refine ⟨GHom.ofMulEquiv E fun g => ?_, GHom.ofMulEquiv_bijective _ _, fun w => ?_, ?_⟩
  · simp [E, e, hτ, toCoprod_of_mem_avoiding T (GX.inl_mem_avoiding x g),
      τ.symm_apply_eq.2 (hτ g).symm]
  · simpa [E, e] using
      DFunLike.congr_fun (eval_comp_toCoprod hσx (hT' (Set.mem_insert s S))) (τ w)
  · simp [E, e, hs, toCoprod_inr_self]

end Elimination

/-- **Eliminating a relator which is a basis element.** Let `τ` be a coefficient-fixing
automorphism of `G[X]` under which the relator `s` becomes `u x v`, where the variable `x` occurs
neither in `u` and `v` nor in the images of the relators of `S`, and let `T` present the same group
as `S` together with `s`. Then `G_S ≅ G_T ∗ ⟨z⟩` over `G`, by an isomorphism sending `s` to `z`
after which sending `z` to `1` is the map `G_S → G_T` induced by the identity of `G[X]`. -/
theorem exists_bijective_of_normalClosure_eq_insert {S T : Set (GX G X)} {s u v : GX G X} {x : X}
    (τ : MulAut (GX G X)) (hτ : ∀ g, τ (inl g) = inl g) (hu : u ∈ GX.avoiding x)
    (hv : v ∈ GX.avoiding x) (hs : τ s = u * inr (FreeGroup.of x) * v)
    (hS : ∀ t ∈ S, τ t ∈ GX.avoiding x) (hT : normalClosure T = normalClosure (insert s S)) :
    ∃ e : GHom (coeff S) ((inl : SystemGroup G T →* GX (SystemGroup G T) Unit).comp (coeff T)),
      Function.Bijective e ∧ (∀ w : GX G X,
        eval (MonoidHom.id (SystemGroup G T)) (fun _ => 1) (e (w : SystemGroup G S)) =
          (w : SystemGroup G T)) ∧ e (s : SystemGroup G S) = inr (FreeGroup.of ()) := by
  -- Compose `τ` with the transvection `x ↦ u⁻¹ x v⁻¹`, which sends `u x v` to `x`.
  refine exists_bijective_of_apply_eq (x := x)
    (τ := GX.transvection x u⁻¹ v⁻¹ (inv_mem hu) (inv_mem hv) * τ) (fun g => by simp [hτ]) ?_
    (fun t ht => ?_) hT
  · simp [hs, hu, hv, mul_assoc]
  · simp [hS t ht]

end SystemGroup

end TauCeti.GroupAlgGeom
