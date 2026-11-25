/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# Fibre products of rings

For ring homomorphisms `f : R →+* T` and `g : S →+* T`, Mathlib's `RingHom.pullback f g` is the
fibre product `R ×_T S`, the subring of pairs `(r, s)` of `R × S` with `f r = g s`, with
projections `RingHom.pullbackFst f g` and `RingHom.pullbackSnd f g`. The rings need not be
commutative. This file develops its universal property, its functoriality in commuting maps of
cospans, its canonical isomorphisms and its kernels.

A square of rings that is a fibre product, one of whose legs `f`, `g` is surjective, is a
*Milnor square*. Milnor's patching theorem for projective modules and the Mayer–Vietoris
sequence of algebraic K-theory concern such squares. The kernel identifications below turn a
Milnor square into the ideal-square form `I ⊆ D → A₂`, with `I` mapped isomorphically onto an
ideal of `A₁`. When `f` is surjective, so is `pullbackSnd f g` (Mathlib's
`RingHom.surjective_pullbackSnd_of_surjective`), and Mathlib's
`RingHom.quotientKerEquivOfSurjective` then identifies `R ×_T S ⧸ ker (pullbackSnd f g)` with
`S`.

## Main definitions

* `RingHom.pullbackLift`: the homomorphism into `R ×_T S` induced by two homomorphisms that agree
  over `T`.
* `RingHom.pullbackLiftEquiv`: the universal property of `R ×_T S`, as a bijection.
* `RingHom.pullbackMap`: the homomorphism of fibre products induced by a map of cospans.
* `RingHom.pullbackCongr`: the isomorphism of fibre products induced by an isomorphism of
  cospans.
* `RingHom.pullbackComm`: `R ×_T S ≃+* S ×_T R`, swapping the factors.
* `RingHom.pullbackEquivProdOfSubsingleton`: over the zero ring, `R ×_T S` is `R × S`.
* `RingHom.pullbackFstEquiv`, `RingHom.pullbackSndEquiv`: a fibre product along a bijective leg
  is the other factor.
* `RingHom.kerPullbackSndEquiv`, `RingHom.kerPullbackFstEquiv`: the first projection maps the
  kernel of the second projection isomorphically onto `ker f`, and symmetrically.

## Main results

* `RingHom.pullback_hom_ext`: homomorphisms into `R ×_T S` agreeing after both projections are
  equal.
* `RingHom.injective_pullbackFst_of_injective`: if `g` is injective then so is the first
  projection.
* `RingHom.map_pullbackFst_ker_pullbackSnd_eq`: the first projection maps `ker (pullbackSnd)`
  onto `ker f`; this is the counterpart of Mathlib's `RingHom.map_pullbackSnd_ker_pullbackFst_eq`.
* `RingHom.ker_pullbackFst_inf_ker_pullbackSnd`: the two projections are jointly injective.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §2.
* C. Weibel, *The K-book*, Chapter I, §2.6.
-/

public section

namespace RingHom

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T] (f : R →+* T) (g : S →+* T)

/-- The two components of an element of the fibre product agree in `T`: the pointwise form of
Mathlib's `RingHom.pullback_comm_sq`. -/
theorem pullback_comm_sq_apply (x : f.pullback g) : f (x : R × S).1 = g (x : R × S).2 :=
  x.property

/-! ## The universal property -/

section Lift

variable {U : Type*} [NonAssocSemiring U]

/-- The ring homomorphism into the fibre product `R ×_T S` induced by ring homomorphisms
`φ₁ : U →+* R` and `φ₂ : U →+* S` that agree after composing with `f` and `g`. -/
def pullbackLift (φ₁ : U →+* R) (φ₂ : U →+* S) (h : f.comp φ₁ = g.comp φ₂) :
    U →+* f.pullback g :=
  (φ₁.prod φ₂).codRestrict _ fun x ↦ DFunLike.congr_fun h x

variable {f g}

@[simp]
theorem coe_pullbackLift_apply (φ₁ : U →+* R) (φ₂ : U →+* S) (h : f.comp φ₁ = g.comp φ₂)
    (x : U) : (f.pullbackLift g φ₁ φ₂ h x : R × S) = (φ₁ x, φ₂ x) :=
  (rfl)

@[simp]
theorem pullbackFst_comp_pullbackLift (φ₁ : U →+* R) (φ₂ : U →+* S)
    (h : f.comp φ₁ = g.comp φ₂) : (f.pullbackFst g).comp (f.pullbackLift g φ₁ φ₂ h) = φ₁ :=
  (rfl)

@[simp]
theorem pullbackSnd_comp_pullbackLift (φ₁ : U →+* R) (φ₂ : U →+* S)
    (h : f.comp φ₁ = g.comp φ₂) : (f.pullbackSnd g).comp (f.pullbackLift g φ₁ φ₂ h) = φ₂ :=
  (rfl)

/-- Two ring homomorphisms into the fibre product `R ×_T S` are equal when their composites with
both projections are equal. -/
theorem pullback_hom_ext {ψ₁ ψ₂ : U →+* f.pullback g}
    (h₁ : (f.pullbackFst g).comp ψ₁ = (f.pullbackFst g).comp ψ₂)
    (h₂ : (f.pullbackSnd g).comp ψ₁ = (f.pullbackSnd g).comp ψ₂) : ψ₁ = ψ₂ :=
  RingHom.ext fun x ↦ Subtype.ext <| Prod.ext (DFunLike.congr_fun h₁ x) (DFunLike.congr_fun h₂ x)

/-- `RingHom.pullbackLift` is the only homomorphism with the prescribed projections. -/
theorem eq_pullbackLift {φ₁ : U →+* R} {φ₂ : U →+* S} (h : f.comp φ₁ = g.comp φ₂)
    {ψ : U →+* f.pullback g} (h₁ : (f.pullbackFst g).comp ψ = φ₁)
    (h₂ : (f.pullbackSnd g).comp ψ = φ₂) : ψ = f.pullbackLift g φ₁ φ₂ h :=
  pullback_hom_ext h₁ h₂

variable (f g) in
@[simp]
theorem pullbackLift_pullbackFst_pullbackSnd :
    f.pullbackLift g (f.pullbackFst g) (f.pullbackSnd g) (f.pullback_comm_sq g) =
      RingHom.id (f.pullback g) :=
  (rfl)

theorem pullbackLift_comp {V : Type*} [NonAssocSemiring V] (φ₁ : U →+* R) (φ₂ : U →+* S)
    (h : f.comp φ₁ = g.comp φ₂) (ψ : V →+* U) :
    (f.pullbackLift g φ₁ φ₂ h).comp ψ =
      f.pullbackLift g (φ₁.comp ψ) (φ₂.comp ψ) (by rw [← comp_assoc, h, comp_assoc]) :=
  (rfl)

variable (f g U) in
/-- The **universal property of the fibre product**: ring homomorphisms `U →+* R ×_T S`
correspond to pairs of ring homomorphisms `U →+* R` and `U →+* S` that agree over `T`. -/
def pullbackLiftEquiv :
    {φ : (U →+* R) × (U →+* S) // f.comp φ.1 = g.comp φ.2} ≃ (U →+* f.pullback g) where
  toFun φ := f.pullbackLift g φ.val.1 φ.val.2 φ.property
  invFun ψ := ⟨((f.pullbackFst g).comp ψ, (f.pullbackSnd g).comp ψ), by
    rw [← comp_assoc, pullback_comm_sq, comp_assoc]⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem pullbackLiftEquiv_apply (φ : {φ : (U →+* R) × (U →+* S) // f.comp φ.1 = g.comp φ.2}) :
    pullbackLiftEquiv f g U φ = f.pullbackLift g φ.val.1 φ.val.2 φ.property :=
  (rfl)

@[simp]
theorem coe_pullbackLiftEquiv_symm_apply (ψ : U →+* f.pullback g) :
    ((pullbackLiftEquiv f g U).symm ψ : (U →+* R) × (U →+* S)) =
      ((f.pullbackFst g).comp ψ, (f.pullbackSnd g).comp ψ) :=
  (rfl)

end Lift

/-! ## Maps of cospans -/

section Map

variable {R' S' T' : Type*} [Ring R'] [Ring S'] [Semiring T'] (f' : R' →+* T') (g' : S' →+* T')

/-- The homomorphism of fibre products `R ×_T S →+* R' ×_{T'} S'` induced by a commuting map of
cospans, `(r, s) ↦ (a r, b s)`. -/
def pullbackMap (a : R →+* R') (b : S →+* S') (c : T →+* T') (ha : f'.comp a = c.comp f)
    (hb : g'.comp b = c.comp g) : f.pullback g →+* f'.pullback g' :=
  f'.pullbackLift g' (a.comp (f.pullbackFst g)) (b.comp (f.pullbackSnd g)) (by
    rw [← comp_assoc, ha, comp_assoc, pullback_comm_sq, ← comp_assoc, ← hb, comp_assoc])

variable {f g f' g'}

@[simp]
theorem coe_pullbackMap_apply (a : R →+* R') (b : S →+* S') (c : T →+* T')
    (ha : f'.comp a = c.comp f) (hb : g'.comp b = c.comp g) (x : f.pullback g) :
    (f.pullbackMap g f' g' a b c ha hb x : R' × S') = (a (x : R × S).1, b (x : R × S).2) :=
  (rfl)

@[simp]
theorem pullbackFst_comp_pullbackMap (a : R →+* R') (b : S →+* S') (c : T →+* T')
    (ha : f'.comp a = c.comp f) (hb : g'.comp b = c.comp g) :
    (f'.pullbackFst g').comp (f.pullbackMap g f' g' a b c ha hb) = a.comp (f.pullbackFst g) :=
  (rfl)

@[simp]
theorem pullbackSnd_comp_pullbackMap (a : R →+* R') (b : S →+* S') (c : T →+* T')
    (ha : f'.comp a = c.comp f) (hb : g'.comp b = c.comp g) :
    (f'.pullbackSnd g').comp (f.pullbackMap g f' g' a b c ha hb) = b.comp (f.pullbackSnd g) :=
  (rfl)

variable (f g) in
@[simp]
theorem pullbackMap_id (ha : f.comp (RingHom.id R) = (RingHom.id T).comp f)
    (hb : g.comp (RingHom.id S) = (RingHom.id T).comp g) :
    f.pullbackMap g f g (RingHom.id R) (RingHom.id S) (RingHom.id T) ha hb =
      RingHom.id (f.pullback g) :=
  (rfl)

theorem pullbackMap_comp {R'' S'' T'' : Type*} [Ring R''] [Ring S''] [Semiring T'']
    {f'' : R'' →+* T''} {g'' : S'' →+* T''} (a : R →+* R') (b : S →+* S') (c : T →+* T')
    (ha : f'.comp a = c.comp f) (hb : g'.comp b = c.comp g) (a' : R' →+* R'')
    (b' : S' →+* S'') (c' : T' →+* T'') (ha' : f''.comp a' = c'.comp f')
    (hb' : g''.comp b' = c'.comp g') (ha'' : f''.comp (a'.comp a) = (c'.comp c).comp f)
    (hb'' : g''.comp (b'.comp b) = (c'.comp c).comp g) :
    (f'.pullbackMap g' f'' g'' a' b' c' ha' hb').comp (f.pullbackMap g f' g' a b c ha hb) =
      f.pullbackMap g f'' g'' (a'.comp a) (b'.comp b) (c'.comp c) ha'' hb'' :=
  (rfl)

/-- The isomorphism of fibre products `R ×_T S ≃+* R' ×_{T'} S'` induced by an isomorphism of
cospans, `(r, s) ↦ (a r, b s)`. -/
def pullbackCongr (a : R ≃+* R') (b : S ≃+* S') (c : T ≃+* T')
    (ha : f'.comp (a : R →+* R') = (c : T →+* T').comp f)
    (hb : g'.comp (b : S →+* S') = (c : T →+* T').comp g) : f.pullback g ≃+* f'.pullback g' :=
  RingEquiv.ofRingHom (f.pullbackMap g f' g' a b c ha hb)
    (f'.pullbackMap g' f g a.symm b.symm c.symm
      (RingHom.ext fun x ↦ c.injective <| by simpa using (DFunLike.congr_fun ha (a.symm x)).symm)
      (RingHom.ext fun x ↦ c.injective <| by simpa using (DFunLike.congr_fun hb (b.symm x)).symm))
    (pullback_hom_ext (RingHom.ext fun _ ↦ by simp) (RingHom.ext fun _ ↦ by simp))
    (pullback_hom_ext (RingHom.ext fun _ ↦ by simp) (RingHom.ext fun _ ↦ by simp))

@[simp]
theorem coe_pullbackCongr_apply (a : R ≃+* R') (b : S ≃+* S') (c : T ≃+* T')
    (ha : f'.comp (a : R →+* R') = (c : T →+* T').comp f)
    (hb : g'.comp (b : S →+* S') = (c : T →+* T').comp g) (x : f.pullback g) :
    (pullbackCongr a b c ha hb x : R' × S') = (a (x : R × S).1, b (x : R × S).2) :=
  (rfl)

@[simp]
theorem coe_pullbackCongr_symm_apply (a : R ≃+* R') (b : S ≃+* S') (c : T ≃+* T')
    (ha : f'.comp (a : R →+* R') = (c : T →+* T').comp f)
    (hb : g'.comp (b : S →+* S') = (c : T →+* T').comp g) (x : f'.pullback g') :
    ((pullbackCongr a b c ha hb).symm x : R × S) =
      (a.symm (x : R' × S').1, b.symm (x : R' × S').2) :=
  (rfl)

end Map

/-! ## Canonical isomorphisms -/

/-- The fibre product is symmetric: `R ×_T S ≃+* S ×_T R`, `(r, s) ↦ (s, r)`. -/
def pullbackComm : f.pullback g ≃+* g.pullback f :=
  RingEquiv.ofRingHom
    (g.pullbackLift f (f.pullbackSnd g) (f.pullbackFst g) (f.pullback_comm_sq g).symm)
    (f.pullbackLift g (g.pullbackSnd f) (g.pullbackFst f) (g.pullback_comm_sq f).symm) rfl rfl

@[simp]
theorem coe_pullbackComm_apply (x : f.pullback g) :
    (pullbackComm f g x : S × R) = (x : R × S).swap :=
  (rfl)

@[simp]
theorem pullbackComm_symm : (pullbackComm f g).symm = pullbackComm g f :=
  (rfl)

/-- Over a zero ring `T` the fibre product `R ×_T S` is the whole product `R × S`. -/
def pullbackEquivProdOfSubsingleton [Subsingleton T] : f.pullback g ≃+* R × S :=
  (RingEquiv.subringCongr (eq_top_iff.2 fun _ _ ↦ Subsingleton.elim _ _)).trans Subring.topEquiv

@[simp]
theorem pullbackEquivProdOfSubsingleton_apply [Subsingleton T] (x : f.pullback g) :
    pullbackEquivProdOfSubsingleton f g x = x :=
  (rfl)

@[simp]
theorem coe_pullbackEquivProdOfSubsingleton_symm_apply [Subsingleton T] (x : R × S) :
    ((pullbackEquivProdOfSubsingleton f g).symm x : R × S) = x :=
  (rfl)

variable {f g}

/-- If `g` is injective, the first projection of `R ×_T S` is injective: the second component of
an element is determined by the first. -/
theorem injective_pullbackFst_of_injective (hg : Function.Injective g) :
    Function.Injective (f.pullbackFst g) := fun x y hxy ↦
  Subtype.ext <| Prod.ext hxy <| hg <| by
    rw [← pullback_comm_sq_apply, ← pullback_comm_sq_apply]
    exact congrArg f hxy

/-- If `f` is injective, the second projection of `R ×_T S` is injective. -/
theorem injective_pullbackSnd_of_injective (hf : Function.Injective f) :
    Function.Injective (f.pullbackSnd g) := fun x y hxy ↦
  Subtype.ext <| Prod.ext (hf <| by
    rw [pullback_comm_sq_apply, pullback_comm_sq_apply]
    exact congrArg g hxy) hxy

variable (f g)

/-- If `g` is bijective, the first projection identifies `R ×_T S` with `R`. -/
noncomputable def pullbackFstEquiv (hg : Function.Bijective g) : f.pullback g ≃+* R :=
  RingEquiv.ofBijective (f.pullbackFst g)
    ⟨injective_pullbackFst_of_injective hg.1, surjective_pullbackFst_of_surjective f g hg.2⟩

@[simp]
theorem coe_pullbackFstEquiv (hg : Function.Bijective g) :
    ⇑(f.pullbackFstEquiv g hg) = f.pullbackFst g :=
  (rfl)

/-- The first projection of the preimage of `r` under `pullbackFstEquiv` is `r`. -/
@[simp]
theorem pullbackFst_pullbackFstEquiv_symm_apply (hg : Function.Bijective g) (r : R) :
    f.pullbackFst g ((f.pullbackFstEquiv g hg).symm r) = r :=
  (f.pullbackFstEquiv g hg).apply_symm_apply r

/-- If `f` is bijective, the second projection identifies `R ×_T S` with `S`. -/
noncomputable def pullbackSndEquiv (hf : Function.Bijective f) : f.pullback g ≃+* S :=
  RingEquiv.ofBijective (f.pullbackSnd g)
    ⟨injective_pullbackSnd_of_injective hf.1, surjective_pullbackSnd_of_surjective f g hf.2⟩

@[simp]
theorem coe_pullbackSndEquiv (hf : Function.Bijective f) :
    ⇑(f.pullbackSndEquiv g hf) = f.pullbackSnd g :=
  (rfl)

/-- The second projection of the preimage of `s` under `pullbackSndEquiv` is `s`. -/
@[simp]
theorem pullbackSnd_pullbackSndEquiv_symm_apply (hf : Function.Bijective f) (s : S) :
    f.pullbackSnd g ((f.pullbackSndEquiv g hf).symm s) = s :=
  (f.pullbackSndEquiv g hf).apply_symm_apply s

/-! ## Kernels of the projections -/

/-- The two projections of the fibre product are jointly injective. -/
theorem ker_pullbackFst_inf_ker_pullbackSnd :
    ker (f.pullbackFst g) ⊓ ker (f.pullbackSnd g) = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  simp only [Submodule.mem_inf, mem_ker] at hx
  exact (Submodule.mem_bot _).2 (Subtype.ext (Prod.ext hx.1 hx.2))

variable {f g} in
private theorem pullbackFst_mem_ker {x : f.pullback g} (hx : x ∈ ker (f.pullbackSnd g)) :
    f.pullbackFst g x ∈ ker f := by
  have h : (x : R × S).2 = 0 := mem_ker.1 hx
  exact mem_ker.2 ((pullback_comm_sq_apply f g x).trans (by rw [h, map_zero]))

variable {f g} in
private theorem pullbackSnd_mem_ker {x : f.pullback g} (hx : x ∈ ker (f.pullbackFst g)) :
    f.pullbackSnd g x ∈ ker g := by
  have h : (x : R × S).1 = 0 := mem_ker.1 hx
  exact mem_ker.2 ((pullback_comm_sq_apply f g x).symm.trans (by rw [h, map_zero]))

/-- The first projection maps the kernel of the second projection onto `ker f`. -/
@[simp]
theorem map_pullbackFst_ker_pullbackSnd_eq :
    Ideal.map (f.pullbackFst g) (ker (f.pullbackSnd g)) = ker f := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun _ hx ↦ pullbackFst_mem_ker hx)
    fun r hr ↦ ?_
  exact Ideal.mem_map_of_mem (f.pullbackFst g) (x := ⟨(r, 0), by simpa using hr⟩)
    (I := ker (f.pullbackSnd g)) (by simp)

/-- The first projection restricts to an additive isomorphism from the kernel of the second
projection onto `ker f`, `(r, 0) ↦ r`. -/
def kerPullbackSndEquiv : ker (f.pullbackSnd g) ≃+ ker f where
  toFun x := ⟨f.pullbackFst g x, pullbackFst_mem_ker x.property⟩
  invFun r := ⟨⟨((r : R), 0), by simpa using mem_ker.1 r.property⟩, by simp⟩
  left_inv x := Subtype.ext <| Subtype.ext <| Prod.ext rfl (mem_ker.1 x.property).symm
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_kerPullbackSndEquiv_apply (x : ker (f.pullbackSnd g)) :
    (kerPullbackSndEquiv f g x : R) = ((x : f.pullback g) : R × S).1 :=
  (rfl)

@[simp]
theorem coe_coe_kerPullbackSndEquiv_symm_apply (r : ker f) :
    (((kerPullbackSndEquiv f g).symm r : f.pullback g) : R × S) = ((r : R), 0) :=
  (rfl)

/-- The second projection restricts to an additive isomorphism from the kernel of the first
projection onto `ker g`, `(0, s) ↦ s`. -/
def kerPullbackFstEquiv : ker (f.pullbackFst g) ≃+ ker g where
  toFun x := ⟨f.pullbackSnd g x, pullbackSnd_mem_ker x.property⟩
  invFun s := ⟨⟨(0, (s : S)), by simpa [eq_comm] using mem_ker.1 s.property⟩, by simp⟩
  left_inv x := Subtype.ext <| Subtype.ext <| Prod.ext (mem_ker.1 x.property).symm rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_kerPullbackFstEquiv_apply (x : ker (f.pullbackFst g)) :
    (kerPullbackFstEquiv f g x : S) = ((x : f.pullback g) : R × S).2 :=
  (rfl)

@[simp]
theorem coe_coe_kerPullbackFstEquiv_symm_apply (s : ker g) :
    (((kerPullbackFstEquiv f g).symm s : f.pullback g) : R × S) = (0, (s : S)) :=
  (rfl)

end RingHom
