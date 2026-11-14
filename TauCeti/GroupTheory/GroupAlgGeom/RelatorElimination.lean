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
Suppose that after an automorphism `τ` of `G[X]` the relator `s` becomes `u x v`
for a variable `x` occurring neither in the words `u`, `v` nor in the images of the relators of
`S`; that is, `s` belongs to a free basis of `G[X]` over `G` whose other members generate, together
with `G`, a free factor containing `S`. Then adding `s` to `S` kills a free factor: the group
`G_S = G[X] ⧸ ncl(S)` presented by `S` is the free product of the group `G_T` presented by `S` and
`s` with an infinite cyclic group `⟨z⟩` (`TauCeti.GroupAlgGeom.SystemGroup.elimEquiv`). Under this
isomorphism `s` corresponds to `z` and the class of a word whose image under `τ` avoids `x`
corresponds to its class in `G_T`; sending `z` to `1` gives back the quotient map. In `G_T` the
classes of these words generate, the remaining generator `τ⁻¹ x` being `τ⁻¹ (u⁻¹ v⁻¹)` there
(`TauCeti.GroupAlgGeom.SystemGroup.mk_symm_inr_of_eq`).

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

/-- The homomorphism `G_S → G_T ∗ ⟨z⟩` induced by `toCoprod ∘ τ`. -/
private def elimHom (τ : MulAut (GX G X)) (x : X) (hS : ∀ t ∈ S, τ t ∈ GX.avoiding x)
    (hT : S ⊆ normalClosure T) : SystemGroup G S →* GX (SystemGroup G T) Unit :=
  QuotientGroup.lift _ ((toCoprod τ x T).comp τ.toMonoidHom) <| normalClosure_le_normal
    fun t ht => by
      rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        toCoprod_of_mem_avoiding T (hS t ht)]
      simp [(QuotientGroup.eq_one_iff t).2 (hT ht)]

/-- The homomorphism `G_T → G_S` induced by `retract ∘ τ`. -/
private def elimInvHom (hs : τ s = inr (FreeGroup.of x)) (hS : ∀ t ∈ S, τ t ∈ GX.avoiding x)
    (hT : normalClosure T = normalClosure (insert s S)) : SystemGroup G T →* SystemGroup G S :=
  QuotientGroup.lift _ ((retract τ x S).comp τ.toMonoidHom) <| hT ▸ normalClosure_le_normal (by
    rintro t (rfl | ht) <;>
      rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    · rw [hs, retract_inr_self]
    · rw [retract_of_mem_avoiding S (hS t ht)]
      simpa using (QuotientGroup.eq_one_iff _).2 (subset_normalClosure ht))

/-- The case `τ s = x` of `elimEquiv`. -/
private def elimEquivAux (hs : τ s = inr (FreeGroup.of x)) (hS : ∀ t ∈ S, τ t ∈ GX.avoiding x)
    (hT : normalClosure T = normalClosure (insert s S)) :
    SystemGroup G S ≃* GX (SystemGroup G T) Unit :=
  have hσx : τ.symm (inr (FreeGroup.of x)) = s := τ.symm_apply_eq.2 hs.symm
  have hST : insert s S ⊆ normalClosure T := hT ▸ subset_normalClosure
  have hsT : (s : SystemGroup G T) = 1 := (QuotientGroup.eq_one_iff s).2 (hST (Set.mem_insert s S))
  (elimHom τ x hS ((Set.subset_insert s S).trans hST)).toMulEquiv
    (lift (elimInvHom hs hS hT) (FreeGroup.lift fun _ => (s : SystemGroup G S)))
    (QuotientGroup.monoidHom_ext _ <| MonoidHom.ext fun w => by
      simpa [elimHom] using DFunLike.congr_fun (lift_comp_toCoprod hσx (φ := elimInvHom hs hS hT)
        fun w => QuotientGroup.lift_mk _ _ w) (τ w))
    (hom_ext (QuotientGroup.monoidHom_ext _ <| MonoidHom.ext fun w => by
        simpa [elimInvHom] using DFunLike.congr_fun (comp_retract hσx hsT
          (ψ := elimHom τ x hS ((Set.subset_insert s S).trans hST))
          fun w => QuotientGroup.lift_mk _ _ w) (τ w))
      (FreeGroup.ext_hom _ _ fun _ => by simp [elimHom, hs, toCoprod_inr_self]))

private theorem elimEquivAux_mk (hs : τ s = inr (FreeGroup.of x))
    (hS : ∀ t ∈ S, τ t ∈ GX.avoiding x) (hT : normalClosure T = normalClosure (insert s S))
    (w : GX G X) : elimEquivAux hs hS hT (w : SystemGroup G S) = toCoprod τ x T (τ w) :=
  rfl

end Elimination

section ElimEquiv

variable {S T : Set (GX G X)} {s u v : GX G X} {x : X} (τ : MulAut (GX G X))
  (hu : u ∈ GX.avoiding x) (hv : v ∈ GX.avoiding x) (hs : τ s = u * inr (FreeGroup.of x) * v)
  (hS : ∀ t ∈ S, τ t ∈ GX.avoiding x) (hT : normalClosure T = normalClosure (insert s S))

/-- **Eliminating a relator which is a basis element.** Let `τ` be an automorphism of `G[X]` under
which the relator `s` becomes `u x v`, where the variable `x` occurs neither in `u` and `v` nor in
the images of the relators of `S`, and let `T` present the same group as `S` together with `s`.
Then `G_S ≅ G_T ∗ ⟨z⟩`: the class of a word whose image under `τ` avoids `x` goes to its class in
`G_T`, and the class of `s` goes to `z`. -/
def elimEquiv : SystemGroup G S ≃* GX (SystemGroup G T) Unit :=
  elimEquivAux (τ := GX.transvection x u⁻¹ v⁻¹ (inv_mem hu) (inv_mem hv) * τ) (x := x)
    (by simp [hs, hu, hv, mul_assoc]) (fun t ht => by simp [hS t ht]) hT

/-- The class of a word whose image under `τ` avoids `x` is sent to its class in `G_T`. -/
theorem elimEquiv_mk_of_mem_avoiding {w : GX G X} (hw : τ w ∈ GX.avoiding x) :
    elimEquiv τ hu hv hs hS hT (w : SystemGroup G S) = inl (w : SystemGroup G T) := by
  have hw' : (GX.transvection x u⁻¹ v⁻¹ (inv_mem hu) (inv_mem hv) * τ) w ∈ GX.avoiding x := by
    simp [hw]
  rw [elimEquiv, elimEquivAux_mk, toCoprod_of_mem_avoiding T hw', MulEquiv.symm_apply_apply]

/-- The isomorphism `G_S ≅ G_T ∗ ⟨z⟩` fixes the coefficients which `τ` fixes. -/
theorem elimEquiv_mk_inl {g : G} (hg : τ (inl g) = inl g) :
    elimEquiv τ hu hv hs hS hT ((inl g : GX G X) : SystemGroup G S) =
      inl ((inl g : GX G X) : SystemGroup G T) :=
  elimEquiv_mk_of_mem_avoiding τ hu hv hs hS hT (by simp [hg])

/-- The class of the eliminated relator is sent to the free generator `z`. -/
@[simp]
theorem elimEquiv_mk_self :
    elimEquiv τ hu hv hs hS hT (s : SystemGroup G S) = inr (FreeGroup.of ()) := by
  rw [elimEquiv, elimEquivAux_mk]
  simp [hs, hu, hv, mul_assoc, toCoprod_inr_self]

/-- The free generator `z` corresponds to the class of the eliminated relator. -/
@[simp]
theorem elimEquiv_symm_inr_of :
    (elimEquiv τ hu hv hs hS hT).symm (inr (FreeGroup.of ())) = (s : SystemGroup G S) :=
  (MulEquiv.symm_apply_eq _).2 (elimEquiv_mk_self τ hu hv hs hS hT).symm

/-- The class in `G_T` of a word whose image under `τ` avoids `x` corresponds to its class in
`G_S`. -/
theorem elimEquiv_symm_inl_mk_of_mem_avoiding {w : GX G X} (hw : τ w ∈ GX.avoiding x) :
    (elimEquiv τ hu hv hs hS hT).symm (inl (w : SystemGroup G T)) = (w : SystemGroup G S) :=
  (MulEquiv.symm_apply_eq _).2 (elimEquiv_mk_of_mem_avoiding τ hu hv hs hS hT hw).symm

/-- Sending `z` to `1` after the isomorphism `G_S ≅ G_T ∗ ⟨z⟩` is the homomorphism `G_S → G_T`
induced by the identity of `G[X]`. -/
@[simp]
theorem eval_elimEquiv_mk (w : GX G X) :
    eval (MonoidHom.id (SystemGroup G T)) (fun _ => 1)
      (elimEquiv τ hu hv hs hS hT (w : SystemGroup G S)) = (w : SystemGroup G T) := by
  have hsT : (s : SystemGroup G T) = 1 :=
    (QuotientGroup.eq_one_iff s).2 (hT ▸ subset_normalClosure (Set.mem_insert s S))
  rw [elimEquiv, elimEquivAux_mk]
  exact (DFunLike.congr_fun (eval_comp_toCoprod
    ((MulEquiv.symm_apply_eq _).2 (by simp [hs, hu, hv, mul_assoc])) hsT) _).trans
      (congrArg _ (MulEquiv.symm_apply_apply _ w))

end ElimEquiv

omit [DecidableEq X] in
/-- If `s = τ⁻¹ (u x v)` is trivial in `G_T`, then `τ⁻¹ x = τ⁻¹ (u⁻¹ v⁻¹)` there: when `x` occurs
neither in `u` nor in `v`, the generator `τ⁻¹ x` is expressed by the remaining ones. -/
theorem mk_symm_inr_of_eq {T : Set (GX G X)} {s u v : GX G X} {x : X} (τ : MulAut (GX G X))
    (hs : τ s = u * inr (FreeGroup.of x) * v) (hsT : s ∈ normalClosure T) :
    ((τ.symm (inr (FreeGroup.of x)) : GX G X) : SystemGroup G T) =
      ((τ.symm (u⁻¹ * v⁻¹) : GX G X) : SystemGroup G T) := by
  have h := (QuotientGroup.eq_one_iff s).2 hsT
  rw [← τ.symm_apply_apply s, hs] at h
  simp only [map_mul, map_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h ⊢
  exact eq_mul_inv_of_mul_eq (eq_inv_of_mul_eq_one_right (by rwa [← mul_assoc]))

end SystemGroup

end TauCeti.GroupAlgGeom
