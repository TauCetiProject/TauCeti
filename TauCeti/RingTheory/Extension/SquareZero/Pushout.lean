/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.Extension.SquareZero

/-!
# Pushout of square-zero extensions along module maps

Let `E` be a square-zero extension of the `A`-algebra `B` by the `B`-module `M`, with projection
`π : E → B` and kernel inclusion `ι : M → E`, and let `f : M → N` be `B`-linear. The pushout
`f_* E` is the square-zero extension of `B` by `N` with ring `(E ⊕ N) / {(ι m, -f m) | m ∈ M}`,
where `E ⊕ N` is the trivial square-zero extension of `E` by `N` (an `E`-module through `π`). It
comes with an `A`-algebra map `E → f_* E` over `B` restricting to `f` on the kernels, and it is
the initial such extension: every `A`-algebra map `g : E → F` to an extension `F` of `B` by `N`
that is compatible with the projections and restricts to `f` on the kernels factors uniquely
through `f_* E`.

Pushout makes `Exal_A(B, M)` covariantly functorial in the `B`-module `M`: a `B`-linear map
`f : M → N` induces `Exal_A(B, M) → Exal_A(B, N)`, which is the identity for `f = id`, respects
composition, and sends the split class to the split class. On derivations, the corresponding map
`Der_A(B, M) → Der_A(B, N)` is Mathlib's `LinearMap.compDer`.

## Main definitions

* `TauCeti.SquareZeroExtension.pushout`: the pushout `f_* E` of an extension along `f : M → N`.
* `TauCeti.SquareZeroExtension.toPushout`: the canonical `A`-algebra map `E → f_* E`.
* `TauCeti.SquareZeroExtension.pushoutDesc`: the morphism `f_* E ⟶ F` induced by a map `E → F`
  over `B` restricting to `f` on the kernels.
* `TauCeti.SquareZeroExtension.Splitting.pushout`: the pushout of a splitting.
* `TauCeti.Exal.map`: the map `Exal_A(B, M) → Exal_A(B, N)` induced by `f : M → N`.

## Main results

* `TauCeti.SquareZeroExtension.pushout_hom_ext`: morphisms out of `f_* E` are determined by
  their composites with `E → f_* E`.
* `TauCeti.Exal.map_id`, `TauCeti.Exal.map_comp`: functoriality of `Exal_A(B, -)`.
* `TauCeti.Exal.map_zero`: the induced map preserves the split class.

## References

* [Stacks Project, Deformation Theory, Section 2, Tag 08S3](https://stacks.math.columbia.edu/tag/08S3):
  pushout of square-zero extensions along module maps and the functoriality of `Exal_A(B, -)`.
-/

public section

universe w w' u v t t'

namespace TauCeti

open CategoryTheory TrivSqZeroExt

namespace SquareZeroExtension

variable {A : Type u} {B : Type v} {M : Type t} {N : Type t'} [CommRing A] [CommRing B]
  [Algebra A B] [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
  (E : SquareZeroExtension.{w} A B M) (f : M →ₗ[B] N)

/-! ### The ring of the pushout

The ring of `f_* E` is a quotient of `TrivSqZeroExt E.Ring N`, for which `N` is made an
`E.Ring`-bimodule through `π`, and its `A`-algebra structure comes from `A → E.Ring`. These
structures are only local instances, used to build the pushout ring; they are not exported. -/

/-- `N` as an `E.Ring`-module through the projection `π`. -/
private abbrev moduleRing : Module E.Ring N :=
  Module.compHom N E.π.toRingHom

/-- `N` as a right `E.Ring`-module through the projection `π`. -/
private abbrev moduleRingOp : Module E.Ringᵐᵒᵖ N :=
  Module.compHom N (E.π.toRingHom.fromOpposite fun _ _ ↦ .all _ _)

attribute [local instance] moduleRing moduleRingOp

private theorem ring_smul_def (x : E.Ring) (n : N) : x • n = E.π x • n :=
  rfl

private abbrev isCentralScalarRing : IsCentralScalar E.Ring N :=
  ⟨fun _ _ ↦ rfl⟩

attribute [local instance] isCentralScalarRing

/-- The ideal `{(ι m, -f m) | m ∈ M}` of `TrivSqZeroExt E.Ring N` divided out by the pushout. -/
private def pushoutIdeal : Ideal (TrivSqZeroExt E.Ring N) where
  carrier := Set.range fun m ↦ inl (E.ι m) - inr (f m)
  add_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨m', rfl⟩
    exact ⟨m + m', by simp only [map_add, inl_add, inr_add]; abel⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro x _ ⟨m, rfl⟩
    refine ⟨E.π x.fst • m, ?_⟩
    ext
    · simp [mul_sub]
    · simp [mul_sub, ring_smul_def]

private theorem mem_pushoutIdeal {z : TrivSqZeroExt E.Ring N} :
    z ∈ pushoutIdeal E f ↔ ∃ m, inl (E.ι m) - inr (f m) = z :=
  Iff.rfl

/-- The ring of the pushout `f_* E`. -/
private abbrev PushoutRing : Type _ :=
  TrivSqZeroExt E.Ring N ⧸ pushoutIdeal E f

/-- The `A`-algebra structure on the pushout ring, through `A → E.Ring`. -/
private abbrev algebraPushoutRing : Algebra A (PushoutRing E f) :=
  Algebra.compHom _ (algebraMap A E.Ring)

attribute [local instance] algebraPushoutRing

private theorem algebraMap_pushoutRing (a : A) :
    algebraMap A (PushoutRing E f) a = Ideal.Quotient.mk _ (inl (algebraMap A E.Ring a)) :=
  rfl

/-- The `A`-algebra map `(x, n) ↦ π x` on the pushout ring. -/
private def pushoutπ : PushoutRing E f →ₐ[A] B where
  toRingHom := Ideal.Quotient.lift _ (E.π.toRingHom.comp (fstHom E.Ring E.Ring N).toRingHom) <| by
    rintro _ ⟨m, rfl⟩
    simp
  commutes' a := E.π.commutes a

private theorem pushoutπ_mk (z : TrivSqZeroExt E.Ring N) :
    pushoutπ E f (Ideal.Quotient.mk _ z) = E.π z.fst :=
  rfl

/-- The pushout `f_* E` of a square-zero extension `E` of `B` by `M` along a `B`-linear map
`f : M → N`: the square-zero extension of `B` by `N` whose ring is `(E ⊕ N) / {(ι m, -f m)}`.
It is the initial extension of `B` by `N` receiving an `A`-algebra map from `E` over `B` that
restricts to `f` on the kernels (`TauCeti.SquareZeroExtension.pushoutDesc`). -/
noncomputable def pushout : SquareZeroExtension.{max w t'} A B N where
  Ring := PushoutRing E f
  π := pushoutπ E f
  π_surjective b := by
    obtain ⟨x, rfl⟩ := E.π_surjective b
    exact ⟨Ideal.Quotient.mk _ (inl x), pushoutπ_mk E f _⟩
  ι := (Ideal.Quotient.mk _).toAddMonoidHom.comp (inrHom E.Ring N).toAddMonoidHom
  ι_injective := by
    refine (injective_iff_map_eq_zero _).2 fun n hn ↦ ?_
    obtain ⟨m, hm⟩ := (mem_pushoutIdeal E f).1 (Ideal.Quotient.eq_zero_iff_mem.1 hn)
    obtain rfl : m = 0 := by simpa using congr(fst $hm)
    simpa using congr(snd $hm).symm
  exact z := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [pushoutπ_mk]
    refine ⟨fun hz ↦ ?_, fun ⟨n, hn⟩ ↦ ?_⟩
    · obtain ⟨m, hm⟩ := (E.exact z.fst).1 hz
      refine ⟨z.snd + f m, Ideal.Quotient.eq.2 ⟨-m, ?_⟩⟩
      ext <;> simp [hm]
    · -- `ι n` is by definition the class of `inr n`.
      obtain ⟨m, hm⟩ := (mem_pushoutIdeal E f).1 <| Ideal.Quotient.eq.1
        (hn.symm : Ideal.Quotient.mk _ z = Ideal.Quotient.mk _ (inr n))
      have hm : E.ι m = z.fst := by simpa using congr(fst $hm)
      rw [← hm, π_ι]
  mul_ι z n := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    have : z * inr n = inr (E.π z.fst • n) := by
      ext <;> simp [ring_smul_def]
    exact (map_mul (Ideal.Quotient.mk _) z (inr n)).symm.trans congr(Ideal.Quotient.mk _ $this)

/-- The quotient map onto the ring of the pushout. -/
private def mkPushout : TrivSqZeroExt E.Ring N →+* (E.pushout f).Ring :=
  Ideal.Quotient.mk (pushoutIdeal E f)

private theorem mkPushout_surjective : Function.Surjective (mkPushout E f) :=
  Ideal.Quotient.mk_surjective

private theorem mkPushout_eq_zero_iff {z : TrivSqZeroExt E.Ring N} :
    mkPushout E f z = 0 ↔ z ∈ pushoutIdeal E f :=
  Ideal.Quotient.eq_zero_iff_mem

private theorem π_mkPushout (z : TrivSqZeroExt E.Ring N) :
    (E.pushout f).π (mkPushout E f z) = E.π z.fst :=
  rfl

private theorem ι_pushout (n : N) : (E.pushout f).ι n = mkPushout E f (inr n) :=
  rfl

private theorem algebraMap_pushout (a : A) :
    algebraMap A (E.pushout f).Ring a = mkPushout E f (inl (algebraMap A E.Ring a)) :=
  rfl

/-- The canonical `A`-algebra map `E → f_* E`, sending `x` to the class of `(x, 0)`. -/
noncomputable def toPushout : E.Ring →ₐ[A] (E.pushout f).Ring where
  toRingHom := (mkPushout E f).comp (inlHom E.Ring N)
  commutes' _ := rfl

private theorem toPushout_apply (x : E.Ring) : E.toPushout f x = mkPushout E f (inl x) :=
  rfl

@[simp]
theorem π_toPushout (x : E.Ring) : (E.pushout f).π (E.toPushout f x) = E.π x := by
  rw [toPushout_apply, π_mkPushout, fst_inl]

@[simp]
theorem toPushout_ι (m : M) : E.toPushout f (E.ι m) = (E.pushout f).ι (f m) := by
  rw [toPushout_apply, ι_pushout, ← sub_eq_zero, ← map_sub, mkPushout_eq_zero_iff]
  exact ⟨m, rfl⟩

/-- Every element of the pushout is `toPushout x + ι n` for some `x ∈ E` and `n ∈ N`. -/
theorem exists_toPushout_add_ι (z : (E.pushout f).Ring) :
    ∃ x n, E.toPushout f x + (E.pushout f).ι n = z := by
  obtain ⟨z, rfl⟩ := mkPushout_surjective E f z
  exact ⟨z.fst, z.snd, by rw [toPushout_apply, ι_pushout, ← map_add, inl_fst_add_inr_snd_eq]⟩

variable {E f}

/-- Morphisms out of the pushout are determined by their composites with `E → f_* E`. -/
theorem pushout_hom_ext {F : SquareZeroExtension.{max w t'} A B N} {φ ψ : E.pushout f ⟶ F}
    (h : ∀ x, φ.toAlgHom (E.toPushout f x) = ψ.toAlgHom (E.toPushout f x)) : φ = ψ := by
  ext z
  obtain ⟨x, n, rfl⟩ := E.exists_toPushout_add_ι f z
  simp only [map_add, h, Hom.toAlgHom_ι]

/-- For a map `g : E → F` over `B`, multiplication by `g x` on the kernel `ι N` of `F` is the
action of `π x`: the compatibility making `(x, n) ↦ g x + ι n` multiplicative. -/
private theorem ι_smul_eq_mul {F : SquareZeroExtension.{w'} A B N} {g : E.Ring →ₐ[A] F.Ring}
    (hπ : ∀ x, F.π (g x) = E.π x) (x : E.Ring) (n : N) :
    F.ι.toIntLinearMap (x • n) = g.toRingHom.toIntAlgHom x * F.ι.toIntLinearMap n := by
  simp [ring_smul_def, hπ]

/-- The ring map `f_* E → F` sending the class of `(x, n)` to `g x + ι n`, induced by
Mathlib's universal property `TrivSqZeroExt.lift` of `E ⊕ N`. -/
private def descRingHom (F : SquareZeroExtension.{w'} A B N) (g : E.Ring →ₐ[A] F.Ring)
    (hπ : ∀ x, F.π (g x) = E.π x) (hι : ∀ m, g (E.ι m) = F.ι (f m)) :
    PushoutRing E f →+* F.Ring :=
  Ideal.Quotient.lift (pushoutIdeal E f)
    (TrivSqZeroExt.lift g.toRingHom.toIntAlgHom F.ι.toIntLinearMap (fun _ _ ↦ by simp)
      (ι_smul_eq_mul hπ) fun x n ↦ by rw [mul_comm]; exact ι_smul_eq_mul hπ x n).toRingHom <| by
      rintro _ ⟨m, rfl⟩
      simp [lift_def, hι]

private theorem descRingHom_mk (F : SquareZeroExtension.{w'} A B N)
    (g : E.Ring →ₐ[A] F.Ring) (hπ : ∀ x, F.π (g x) = E.π x) (hι : ∀ m, g (E.ι m) = F.ι (f m))
    (z : TrivSqZeroExt E.Ring N) :
    descRingHom F g hπ hι (Ideal.Quotient.mk _ z) = g z.fst + F.ι z.snd := by
  rw [descRingHom, Ideal.Quotient.lift_mk]
  simp [lift_def]

/-- The `A`-algebra map `f_* E → F` sending the class of `(x, n)` to `g x + ι n`. -/
private def descAlgHom (F : SquareZeroExtension.{w'} A B N) (g : E.Ring →ₐ[A] F.Ring)
    (hπ : ∀ x, F.π (g x) = E.π x) (hι : ∀ m, g (E.ι m) = F.ι (f m)) :
    (E.pushout f).Ring →ₐ[A] F.Ring where
  toRingHom := descRingHom F g hπ hι
  -- `algebraMap A (E.pushout f).Ring a` is the class of `inl (algebraMap A E.Ring a)`, as
  -- recorded by `algebraMap_pushout`.
  commutes' a := (descRingHom_mk F g hπ hι (inl (algebraMap A E.Ring a))).trans (by simp)

private theorem descAlgHom_mkPushout (F : SquareZeroExtension.{w'} A B N)
    (g : E.Ring →ₐ[A] F.Ring) (hπ : ∀ x, F.π (g x) = E.π x) (hι : ∀ m, g (E.ι m) = F.ι (f m))
    (z : TrivSqZeroExt E.Ring N) :
    descAlgHom F g hπ hι (mkPushout E f z) = g z.fst + F.ι z.snd :=
  -- `mkPushout E f` is the quotient map `Ideal.Quotient.mk (pushoutIdeal E f)`.
  descRingHom_mk F g hπ hι z

/-- The universal property of the pushout: an `A`-algebra map `g : E → F` to an extension `F`
of `B` by `N`, compatible with the projections and restricting to `f` on the kernels, induces
a morphism of extensions `f_* E ⟶ F`, sending the class of `(x, n)` to `g x + ι n`. -/
noncomputable def pushoutDesc (F : SquareZeroExtension.{max w t'} A B N) (g : E.Ring →ₐ[A] F.Ring)
    (hπ : ∀ x, F.π (g x) = E.π x) (hι : ∀ m, g (E.ι m) = F.ι (f m)) : E.pushout f ⟶ F where
  toAlgHom := descAlgHom F g hπ hι
  π_toAlgHom z := by
    obtain ⟨z, rfl⟩ := mkPushout_surjective E f z
    simp [descAlgHom_mkPushout, π_mkPushout, hπ]
  toAlgHom_ι n := by
    simp [ι_pushout, descAlgHom_mkPushout]

@[simp]
theorem pushoutDesc_toPushout (F : SquareZeroExtension.{max w t'} A B N) (g : E.Ring →ₐ[A] F.Ring)
    (hπ : ∀ x, F.π (g x) = E.π x) (hι : ∀ m, g (E.ι m) = F.ι (f m)) (x : E.Ring) :
    (pushoutDesc F g hπ hι).toAlgHom (E.toPushout f x) = g x := by
  simp [pushoutDesc, toPushout_apply, descAlgHom_mkPushout]

variable (f) in
/-- The morphism of pushouts `f_* E ⟶ f_* E'` induced by a morphism of extensions `E ⟶ E'`. -/
noncomputable def pushoutMap {E' : SquareZeroExtension.{w} A B M} (h : E ⟶ E') :
    E.pushout f ⟶ E'.pushout f :=
  pushoutDesc _ ((E'.toPushout f).comp h.toAlgHom) (by simp) (by simp)

@[simp]
theorem pushoutMap_toPushout {E' : SquareZeroExtension.{w} A B M} (h : E ⟶ E') (x : E.Ring) :
    (pushoutMap f h).toAlgHom (E.toPushout f x) = E'.toPushout f (h.toAlgHom x) := by
  simp [pushoutMap]

@[simp]
theorem pushoutMap_id : pushoutMap f (𝟙 E) = 𝟙 (E.pushout f) :=
  pushout_hom_ext fun _ ↦ by simp

@[simp]
theorem pushoutMap_comp {E' E'' : SquareZeroExtension.{w} A B M} (h : E ⟶ E') (h' : E' ⟶ E'') :
    pushoutMap f (h ≫ h') = pushoutMap f h ≫ pushoutMap f h' :=
  pushout_hom_ext fun _ ↦ by simp

variable (f) in
/-- The pushout of a splitting of `E` along `f` is a splitting of `f_* E`. -/
noncomputable def Splitting.pushout (s : E.Splitting) : (E.pushout f).Splitting where
  toAlgHom := (E.toPushout f).comp s.toAlgHom
  π_toAlgHom b := by simp

@[simp]
theorem Splitting.pushout_toAlgHom (s : E.Splitting) :
    (s.pushout f).toAlgHom = (E.toPushout f).comp s.toAlgHom :=
  (rfl)

end SquareZeroExtension

namespace Exal

open SquareZeroExtension

variable {A : Type u} {B : Type v} {M N P : Type t} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [AddCommGroup P] [Module B P]

/-- The map `Exal_A(B, M) → Exal_A(B, N)` induced by a `B`-linear map `f : M → N`, sending the
class of an extension `E` to the class of its pushout `f_* E`. -/
noncomputable def map (f : M →ₗ[B] N) : Exal A B M → Exal A B N :=
  Exal.lift (fun E ↦ (E.pushout f).extensionClass) fun _ _ ⟨h⟩ ↦
    extensionClass_eq_extensionClass_iff.2 ⟨pushoutMap f h⟩

@[simp]
theorem map_extensionClass (f : M →ₗ[B] N) (E : SquareZeroExtension.{max v t} A B M) :
    map f E.extensionClass = (E.pushout f).extensionClass :=
  lift_extensionClass _ _ E

@[simp]
theorem map_id (x : Exal A B M) : map LinearMap.id x = x := by
  induction x using Exal.ind with
  | h E =>
    rw [map_extensionClass, extensionClass_eq_extensionClass_iff]
    exact ⟨pushoutDesc E (AlgHom.id A E.Ring) (fun _ ↦ rfl) fun _ ↦ rfl⟩

theorem map_comp (g : N →ₗ[B] P) (f : M →ₗ[B] N) (x : Exal A B M) :
    map (g ∘ₗ f) x = map g (map f x) := by
  induction x using Exal.ind with
  | h E =>
    rw [map_extensionClass, map_extensionClass, map_extensionClass,
      extensionClass_eq_extensionClass_iff]
    exact ⟨pushoutDesc _ (((E.pushout f).toPushout g).comp (E.toPushout f)) (by simp) (by simp)⟩

variable [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module A M] [IsScalarTower A B M]
  [IsScalarTower A Bᵐᵒᵖ M] [Module Bᵐᵒᵖ N] [IsCentralScalar B N] [Module A N]
  [IsScalarTower A B N] [IsScalarTower A Bᵐᵒᵖ N]

/-- The map induced on `Exal` by a module map preserves the split class. -/
@[simp]
theorem map_zero (f : M →ₗ[B] N) : map f (0 : Exal A B M) = 0 := by
  rw [← extensionClass_squareZero, map_extensionClass, extensionClass_eq_zero_iff]
  exact ⟨(squareZeroSplitting A B M).pushout f⟩

end Exal

end TauCeti
