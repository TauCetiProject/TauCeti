/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Pullback
public import TauCeti.RingTheory.Extension.SquareZero

/-!
# The Baer sum of square-zero extensions

Let `A → B` be a map of commutative rings and `M` a `B`-module. The Baer sum of two square-zero
extensions `E` and `F` of `B` by `M` over `A` is the quotient of the fibre product
`E ×_B F = {(e, f) | π e = π f}` by the antidiagonal `{(ι m, -ι m)}`, an ideal of the fibre
product. It projects to `B` by `(e, f) ↦ π e`, and `M` is identified with its kernel by
`m ↦ (ι m, 0)`; the class of `(ι m, ι n)` is the kernel element `m + n`.

The Baer sum is functorial in morphisms of extensions, so it descends to the set
`Exal_A(B, M)` of isomorphism classes, and makes it an abelian group. The zero is the class of the
trivial extension `TrivSqZeroExt B M`, the negative of the class of `E` is the class of the
extension `E.neg` with the same ring and the negated kernel identification, and associativity
compares both iterated sums with the triple fibre product. This is the group structure on
`Exal_A(B, M)` under which it is compared with `Ext¹` of the cotangent complex.

## Main definitions

* `TauCeti.SquareZeroExtension.baerSum`: the Baer sum of two square-zero extensions.
* `TauCeti.SquareZeroExtension.toBaerSum`: the quotient map from the fibre product onto the ring of
  the Baer sum.
* `TauCeti.SquareZeroExtension.baerSumDesc`: the universal property of the Baer sum.
* `TauCeti.SquareZeroExtension.baerSumMap`: functoriality of the Baer sum.
* The `AddCommGroup` structure on `TauCeti.Exal A B M`.

## Main results

* `TauCeti.SquareZeroExtension.toBaerSum_ι_ι`: the class of `(ι m, ι n)` is `ι (m + n)`.
* `TauCeti.SquareZeroExtension.toBaerSum_eq_ι_iff`: the elements of the fibre product mapping to
  the kernel element `ι k` are the pairs `(ι m, ι n)` with `m + n = k`.
* `TauCeti.SquareZeroExtension.extensionClass_baerSum`,
  `TauCeti.SquareZeroExtension.extensionClass_neg`: the group operations of `Exal_A(B, M)` on
  representatives.

## References

* [Stacks Project, Deformation Theory, Section 2, Tag 08S3](https://stacks.math.columbia.edu/tag/08S3):
  square-zero extensions of algebras and `Exal_A(B, M)`.
* O. Gabber and L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, Springer,
  2003, §§2.5.4–2.5.7 ([arXiv:math/0201175](https://arxiv.org/abs/math/0201175)): the Baer sum
  of extensions of algebras.
-/

public section

universe w u v t

namespace TauCeti

open CategoryTheory TrivSqZeroExt

namespace SquareZeroExtension

variable {A : Type u} {B : Type v} {M : Type t} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module B M]

section FiberProduct

variable (E F : SquareZeroExtension.{w} A B M)

/-- The antidiagonal `{(ι m, -ι m)}` of the fibre product, an ideal since `E` and `F` induce the
same `B`-module structure on `M`. -/
private def antidiagonal : Ideal (E.π.pullback F.π) where
  carrier := {x | ∃ m, (x : E.Ring × F.Ring) = (E.ι m, -F.ι m)}
  add_mem' := by
    rintro _ _ ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m + n, by simp [hm, hn, add_comm]⟩
  zero_mem' := ⟨0, by simp only [map_zero, neg_zero]; rfl⟩
  smul_mem' := by
    rintro ⟨⟨c, d⟩, hcd⟩ _ ⟨m, hm⟩
    replace hcd : E.π c = F.π d := hcd
    exact ⟨E.π c • m, by simp [hm, hcd]⟩

private theorem mem_antidiagonal {x : E.π.pullback F.π} :
    x ∈ antidiagonal E F ↔ ∃ m, (x : E.Ring × F.Ring) = (E.ι m, -F.ι m) :=
  Iff.rfl

/-- The projection `(e, f) ↦ π e` of the fibre product to `B`. -/
private def fiberProductπ : E.π.pullback F.π →ₐ[A] B :=
  E.π.comp (AlgHom.pullbackFst E.π F.π)

private theorem fiberProductπ_apply (x : E.π.pullback F.π) :
    fiberProductπ E F x = E.π (x : E.Ring × F.Ring).1 :=
  rfl

/-- The inclusion `m ↦ (ι m, 0)` of `M` into the fibre product. -/
private def fiberProductι : M →+ E.π.pullback F.π :=
  AddMonoidHom.mk' (fun m ↦ ⟨(E.ι m, 0), by simp⟩) fun m n ↦ by ext <;> simp

private theorem coe_fiberProductι (m : M) :
    (fiberProductι E F m : E.Ring × F.Ring) = (E.ι m, 0) :=
  rfl

/-- The projection `(e, f) ↦ π e` of the quotient of the fibre product by the antidiagonal. -/
private noncomputable def baerSumπ : (E.π.pullback F.π ⧸ antidiagonal E F) →ₐ[A] B :=
  Ideal.Quotient.liftₐ _ (fiberProductπ E F) <| by
    rintro x ⟨m, hm⟩
    simp [fiberProductπ_apply, hm]

private theorem baerSumπ_mk (x : E.π.pullback F.π) :
    baerSumπ E F (Ideal.Quotient.mk _ x) = E.π (x : E.Ring × F.Ring).1 :=
  rfl

/-- The inclusion `m ↦ (ι m, 0)` of `M` into the quotient of the fibre product by the
antidiagonal. -/
private def baerSumι : M →+ E.π.pullback F.π ⧸ antidiagonal E F :=
  (Ideal.Quotient.mk (antidiagonal E F)).toAddMonoidHom.comp (fiberProductι E F)

private theorem baerSumι_apply (m : M) :
    baerSumι E F m = Ideal.Quotient.mk _ (fiberProductι E F m) :=
  rfl

end FiberProduct

section BaerSum

variable (E F : SquareZeroExtension.{w} A B M)

/-- The Baer sum of two square-zero extensions `E` and `F` of `B` by `M`: the quotient of the
fibre product `E ×_B F` by the antidiagonal `{(ι m, -ι m)}`, projecting to `B` by
`(e, f) ↦ π e`, with `M` included by `m ↦ (ι m, 0)`. -/
noncomputable def baerSum : SquareZeroExtension.{w} A B M where
  Ring := E.π.pullback F.π ⧸ antidiagonal E F
  π := baerSumπ E F
  π_surjective b := by
    obtain ⟨e, rfl⟩ := E.π_surjective b
    obtain ⟨f, hf⟩ := F.π_surjective (E.π e)
    exact ⟨Ideal.Quotient.mk _ ⟨(e, f), hf.symm⟩, rfl⟩
  ι := baerSumι E F
  ι_injective := by
    refine (injective_iff_map_eq_zero _).2 fun m hm ↦ ?_
    rw [baerSumι_apply] at hm
    obtain ⟨k, hk⟩ := (mem_antidiagonal E F).1 (Ideal.Quotient.eq_zero_iff_mem.1 hm)
    rw [coe_fiberProductι, Prod.mk.injEq] at hk
    obtain rfl : k = 0 := by simpa using hk.2.symm
    simpa using hk.1
  exact y := by
    obtain ⟨⟨⟨e, f⟩, hef⟩, rfl⟩ := Ideal.Quotient.mk_surjective y
    replace hef : E.π e = F.π f := hef
    refine ⟨fun h ↦ ?_, ?_⟩
    · rw [baerSumπ_mk] at h
      obtain ⟨m, rfl⟩ := (E.exact e).1 h
      obtain ⟨n, rfl⟩ := (F.exact f).1 (by rw [← hef, h])
      refine ⟨m + n, Ideal.Quotient.eq.2 ⟨n, ?_⟩⟩
      simp [coe_fiberProductι]
    · rintro ⟨m, hm⟩
      rw [← hm, baerSumι_apply, baerSumπ_mk, coe_fiberProductι, π_ι]
  mul_ι y m := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [baerSumι_apply, baerSumι_apply, baerSumπ_mk, ← map_mul]
    congr 1
    ext <;> simp [coe_fiberProductι]

/-- The quotient map from the fibre product `E ×_B F` onto the ring of the Baer sum. -/
noncomputable def toBaerSum : E.π.pullback F.π →ₐ[A] (E.baerSum F).Ring :=
  Ideal.Quotient.mkₐ A (antidiagonal E F)

variable {E F}

theorem toBaerSum_surjective : Function.Surjective (E.toBaerSum F) :=
  Ideal.Quotient.mkₐ_surjective A _

@[simp]
theorem π_toBaerSum (x : E.π.pullback F.π) :
    (E.baerSum F).π (E.toBaerSum F x) = E.π (x : E.Ring × F.Ring).1 :=
  (rfl)

/-- The class of `(ι m, ι n)` in the Baer sum is the kernel element `m + n`. -/
@[simp]
theorem toBaerSum_ι_ι (m n : M) (h : (E.ι m, F.ι n) ∈ E.π.pullback F.π) :
    E.toBaerSum F ⟨(E.ι m, F.ι n), h⟩ = (E.baerSum F).ι (m + n) :=
  Ideal.Quotient.eq.2 ⟨-n, by simp [coe_fiberProductι]⟩

@[simp]
theorem toBaerSum_ι_zero (m : M) (h : (E.ι m, (0 : F.Ring)) ∈ E.π.pullback F.π) :
    E.toBaerSum F ⟨(E.ι m, 0), h⟩ = (E.baerSum F).ι m := by
  simpa using toBaerSum_ι_ι (E := E) (F := F) m 0 (by simp)

@[simp]
theorem toBaerSum_zero_ι (n : M) (h : ((0 : E.Ring), F.ι n) ∈ E.π.pullback F.π) :
    E.toBaerSum F ⟨(0, F.ι n), h⟩ = (E.baerSum F).ι n := by
  simpa using toBaerSum_ι_ι (E := E) (F := F) 0 n (by simp)

/-- An element `(e, f)` of the fibre product maps to the kernel element `ι k` of the Baer sum
exactly when `e = ι m` and `f = ι n` with `m + n = k`. -/
theorem toBaerSum_eq_ι_iff {x : E.π.pullback F.π} {k : M} :
    E.toBaerSum F x = (E.baerSum F).ι k ↔
      ∃ m n, (x : E.Ring × F.Ring) = (E.ι m, F.ι n) ∧ m + n = k := by
  obtain ⟨⟨e, f⟩, hef⟩ := x
  refine ⟨fun h ↦ ?_, ?_⟩
  · have he : E.π e = 0 := by simpa using congr((E.baerSum F).π $h)
    obtain ⟨m, rfl⟩ := (E.exact e).1 he
    obtain ⟨n, rfl⟩ := (F.exact f).1 (by simpa using ((AlgHom.mem_equalizer _ _ _).1 hef).symm)
    rw [toBaerSum_ι_ι] at h
    exact ⟨m, n, rfl, (E.baerSum F).ι_injective h⟩
  · rintro ⟨m, n, h, rfl⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact toBaerSum_ι_ι m n hef

/-- An element `(e, f)` of the fibre product vanishes in the Baer sum exactly when it lies in the
antidiagonal: `e = ι m` and `f = -ι m`. -/
theorem toBaerSum_eq_zero_iff {x : E.π.pullback F.π} :
    E.toBaerSum F x = 0 ↔ ∃ m, (x : E.Ring × F.Ring) = (E.ι m, -F.ι m) :=
  Ideal.Quotient.eq_zero_iff_mem

/-- Two morphisms out of a Baer sum agree if they agree on the image of the fibre product. -/
theorem baerSum_hom_ext {G : SquareZeroExtension.{w} A B M} {f g : E.baerSum F ⟶ G}
    (h : ∀ x, f.toAlgHom (E.toBaerSum F x) = g.toAlgHom (E.toBaerSum F x)) : f = g :=
  hom_ext fun y ↦ by
    obtain ⟨x, rfl⟩ := toBaerSum_surjective y
    exact h x

end BaerSum

section Descend

variable {E F G : SquareZeroExtension.{w} A B M}

/-- The universal property of the Baer sum: an algebra map `φ` from the fibre product `E ×_B F`
to an extension `G` that kills the antidiagonal, lies over `B` and restricts to the identity of
`M` on `m ↦ (ι m, 0)` induces a morphism of extensions `E + F ⟶ G`. -/
noncomputable def baerSumDesc (φ : E.π.pullback F.π →ₐ[A] G.Ring)
    (hφ : ∀ m, φ ⟨(E.ι m, -F.ι m), by simp⟩ = 0)
    (hπ : ∀ x, G.π (φ x) = E.π (x : E.Ring × F.Ring).1)
    (hι : ∀ m, φ ⟨(E.ι m, 0), by simp⟩ = G.ι m) : E.baerSum F ⟶ G :=
  homOfSurjective (E.toBaerSum F) toBaerSum_surjective φ
    (fun x hx ↦ by
      obtain ⟨m, hm⟩ := toBaerSum_eq_zero_iff.1 hx
      obtain rfl : x = ⟨(E.ι m, -F.ι m), by simp⟩ := Subtype.ext hm
      exact hφ m)
    (fun x ↦ by simp [hπ])
    (fun m ↦ ⟨⟨(E.ι m, 0), by simp⟩, by simp, hι m⟩)

@[simp]
theorem baerSumDesc_toAlgHom_toBaerSum (φ : E.π.pullback F.π →ₐ[A] G.Ring)
    (hφ : ∀ m, φ ⟨(E.ι m, -F.ι m), by simp⟩ = 0)
    (hπ : ∀ x, G.π (φ x) = E.π (x : E.Ring × F.Ring).1)
    (hι : ∀ m, φ ⟨(E.ι m, 0), by simp⟩ = G.ι m) (x : E.π.pullback F.π) :
    (baerSumDesc φ hφ hπ hι).toAlgHom (E.toBaerSum F x) = φ x :=
  homOfSurjective_toAlgHom_apply _ _ _ _ _ _ x

end Descend

section Map

variable {E E' F F' : SquareZeroExtension.{w} A B M}

/-- The map of fibre products `E ×_B F → E' ×_B F'` induced by morphisms of extensions. -/
private noncomputable def fiberProductMap (f : E ⟶ E') (g : F ⟶ F') :
    E.π.pullback F.π →ₐ[A] E'.π.pullback F'.π :=
  ((f.toAlgHom.comp ((AlgHom.fst A _ _).comp (E.π.pullback F.π).val)).prod
    (g.toAlgHom.comp ((AlgHom.snd A _ _).comp (E.π.pullback F.π).val))).codRestrict _ fun x ↦ by
    simpa using (AlgHom.mem_equalizer _ _ _).1 x.prop

private theorem coe_fiberProductMap (f : E ⟶ E') (g : F ⟶ F') (x : E.π.pullback F.π) :
    (fiberProductMap f g x : E'.Ring × F'.Ring) = (f.toAlgHom x.1.1, g.toAlgHom x.1.2) :=
  rfl

/-- The Baer sum is functorial in morphisms of extensions: `(e, f) ↦ (f e, g f)`. -/
noncomputable def baerSumMap (f : E ⟶ E') (g : F ⟶ F') : E.baerSum F ⟶ E'.baerSum F' :=
  baerSumDesc ((E'.toBaerSum F').comp (fiberProductMap f g))
    (fun m ↦ by
      rw [AlgHom.comp_apply, toBaerSum_eq_zero_iff]
      exact ⟨m, by simp [coe_fiberProductMap]⟩)
    (fun x ↦ by simp [coe_fiberProductMap])
    (fun m ↦ by
      rw [AlgHom.comp_apply, toBaerSum_eq_ι_iff]
      exact ⟨m, 0, by simp [coe_fiberProductMap], add_zero m⟩)

@[simp]
theorem baerSumMap_toAlgHom_toBaerSum (f : E ⟶ E') (g : F ⟶ F') (x : E.π.pullback F.π) :
    (baerSumMap f g).toAlgHom (E.toBaerSum F x) =
      E'.toBaerSum F' ⟨(f.toAlgHom x.1.1, g.toAlgHom x.1.2),
        by simpa using (AlgHom.mem_equalizer _ _ _).1 x.prop⟩ :=
  baerSumDesc_toAlgHom_toBaerSum _ _ _ _ x

@[simp]
theorem baerSumMap_id : baerSumMap (𝟙 E) (𝟙 F) = 𝟙 (E.baerSum F) :=
  baerSum_hom_ext fun _ ↦ by simp

@[simp]
theorem baerSumMap_comp {E'' F'' : SquareZeroExtension.{w} A B M} (f : E ⟶ E') (f' : E' ⟶ E'')
    (g : F ⟶ F') (g' : F' ⟶ F'') :
    baerSumMap (f ≫ f') (g ≫ g') = baerSumMap f g ≫ baerSumMap f' g' :=
  baerSum_hom_ext fun _ ↦ by simp

end Map

section GroupLaws

variable {E F G : SquareZeroExtension.{w} A B M}

/-- The swap `(e, f) ↦ (f, e)` of fibre products. -/
private def fiberProductSwap : E.π.pullback F.π →ₐ[A] F.π.pullback E.π :=
  (((AlgHom.snd A _ _).prod (AlgHom.fst A _ _)).comp (E.π.pullback F.π).val).codRestrict _
    fun x ↦ by simpa using x.prop.symm

private theorem fiberProductSwap_apply (x : E.π.pullback F.π) :
    fiberProductSwap x = ⟨(x.1.2, x.1.1), by simpa using x.prop.symm⟩ :=
  rfl

/-- The symmetry `(e, f) ↦ (f, e)` of the Baer sum. -/
private noncomputable def baerSumComm : E.baerSum F ⟶ F.baerSum E :=
  baerSumDesc ((F.toBaerSum E).comp fiberProductSwap)
    (fun m ↦ by
      rw [AlgHom.comp_apply, toBaerSum_eq_zero_iff]
      exact ⟨-m, by simp [fiberProductSwap_apply]⟩)
    (fun x ↦ by simpa [fiberProductSwap_apply] using x.prop.symm)
    (fun m ↦ by simp [fiberProductSwap_apply])

/-- The triple fibre product `E ×_B F ×_B G`. -/
private def tripleFiberProduct (E F G : SquareZeroExtension.{w} A B M) :
    Subalgebra A (E.Ring × F.Ring × G.Ring) :=
  AlgHom.equalizer (E.π.comp (AlgHom.fst _ _ _))
      (F.π.comp ((AlgHom.fst _ _ _).comp (AlgHom.snd _ _ _))) ⊓
    AlgHom.equalizer (F.π.comp ((AlgHom.fst _ _ _).comp (AlgHom.snd _ _ _)))
      (G.π.comp ((AlgHom.snd _ _ _).comp (AlgHom.snd _ _ _)))

private theorem mem_tripleFiberProduct {x : E.Ring × F.Ring × G.Ring} :
    x ∈ tripleFiberProduct E F G ↔ E.π x.1 = F.π x.2.1 ∧ F.π x.2.1 = G.π x.2.2 :=
  Iff.rfl

/-- The projection `(e, f, g) ↦ (e, f)` of the triple fibre product. -/
private def tripleFst : tripleFiberProduct E F G →ₐ[A] E.π.pullback F.π :=
  (((AlgHom.fst _ _ _).prod ((AlgHom.fst _ _ _).comp (AlgHom.snd _ _ _))).comp
    (tripleFiberProduct E F G).val).codRestrict _ fun x ↦ (mem_tripleFiberProduct.1 x.2).1

/-- The projection `(e, f, g) ↦ (f, g)` of the triple fibre product. -/
private def tripleSnd : tripleFiberProduct E F G →ₐ[A] F.π.pullback G.π :=
  ((AlgHom.snd _ _ _).comp (tripleFiberProduct E F G).val).codRestrict _ fun x ↦
    (mem_tripleFiberProduct.1 x.2).2

/-- The map `(e, f, g) ↦ ((e, f), g)` from the triple fibre product to the ring of
`(E + F) + G`. -/
private noncomputable def tripleToBaerSumLeft :
    tripleFiberProduct E F G →ₐ[A] ((E.baerSum F).baerSum G).Ring :=
  ((E.baerSum F).toBaerSum G).comp <| AlgHom.codRestrict
    (((E.toBaerSum F).comp tripleFst).prod
      ((AlgHom.snd _ _ _).comp ((AlgHom.snd _ _ _).comp (tripleFiberProduct E F G).val)))
    _ fun x ↦ (mem_tripleFiberProduct.1 x.2).1.trans (mem_tripleFiberProduct.1 x.2).2

/-- The map `(e, f, g) ↦ (e, (f, g))` from the triple fibre product to the ring of
`E + (F + G)`. -/
private noncomputable def tripleToBaerSumRight :
    tripleFiberProduct E F G →ₐ[A] (E.baerSum (F.baerSum G)).Ring :=
  (E.toBaerSum (F.baerSum G)).comp <|
    (((AlgHom.fst _ _ _).comp (tripleFiberProduct E F G).val).prod
      ((F.toBaerSum G).comp tripleSnd)).codRestrict _ fun x ↦ (mem_tripleFiberProduct.1 x.2).1

private theorem tripleToBaerSumLeft_apply (x : tripleFiberProduct E F G) :
    tripleToBaerSumLeft x = (E.baerSum F).toBaerSum G
      ⟨(E.toBaerSum F ⟨(x.1.1, x.1.2.1), (mem_tripleFiberProduct.1 x.2).1⟩, x.1.2.2),
        by have h := mem_tripleFiberProduct.1 x.2; simpa using h.1.trans h.2⟩ :=
  rfl

private theorem tripleToBaerSumRight_apply (x : tripleFiberProduct E F G) :
    tripleToBaerSumRight x = E.toBaerSum (F.baerSum G)
      ⟨(x.1.1, F.toBaerSum G ⟨(x.1.2.1, x.1.2.2), (mem_tripleFiberProduct.1 x.2).2⟩),
        by simpa using (mem_tripleFiberProduct.1 x.2).1⟩ :=
  rfl

/-- The associativity morphism `(E + F) + G ⟶ E + (F + G)`, compared through the triple fibre
product. -/
private noncomputable def baerSumAssoc : (E.baerSum F).baerSum G ⟶ E.baerSum (F.baerSum G) :=
  homOfSurjective tripleToBaerSumLeft
    (fun y ↦ by
      obtain ⟨⟨⟨u, g⟩, hug⟩, rfl⟩ := toBaerSum_surjective y
      obtain ⟨⟨⟨e, f⟩, hef⟩, rfl⟩ := toBaerSum_surjective u
      replace hug : E.π e = G.π g := hug
      replace hef : E.π e = F.π f := hef
      exact ⟨⟨(e, f, g), mem_tripleFiberProduct.2 ⟨hef, hef.symm.trans hug⟩⟩, rfl⟩)
    tripleToBaerSumRight
    (fun ⟨⟨e, f, g⟩, hx⟩ h ↦ by
      rw [tripleToBaerSumLeft_apply, ← map_zero ((E.baerSum F).baerSum G).ι,
        toBaerSum_eq_ι_iff] at h
      obtain ⟨a, c, h, hac⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h, rfl⟩ := h
      obtain ⟨a₁, a₂, hef, rfl⟩ := toBaerSum_eq_ι_iff.1 h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hef
      rw [tripleToBaerSumRight_apply, ← map_zero (E.baerSum (F.baerSum G)).ι, toBaerSum_eq_ι_iff]
      exact ⟨a₁, a₂ + c, Prod.ext rfl (toBaerSum_ι_ι a₂ c _), by rw [← add_assoc, hac]⟩)
    (fun x ↦ by simp [tripleToBaerSumLeft_apply, tripleToBaerSumRight_apply])
    (fun m ↦ ⟨⟨(E.ι m, 0, 0), by simp [mem_tripleFiberProduct]⟩, by
      rw [tripleToBaerSumLeft_apply, toBaerSum_eq_ι_iff]
      exact ⟨m, 0, Prod.ext (toBaerSum_ι_zero m _) (map_zero _).symm, add_zero m⟩, by
      rw [tripleToBaerSumRight_apply, toBaerSum_eq_ι_iff]
      exact ⟨m, 0, Prod.ext rfl (toBaerSum_eq_ι_iff.2 ⟨0, 0, by simp, add_zero 0⟩), add_zero m⟩⟩)

end GroupLaws

section Split

variable {E F : SquareZeroExtension.{w} A B M}

/-- The morphism `e ↦ (e, s (π e))` from an extension `E` to its Baer sum with an extension `F`
split by `s`. -/
private noncomputable def toBaerSumOfSplitting (s : F.Splitting) : E ⟶ E.baerSum F where
  toAlgHom := (E.toBaerSum F).comp <|
    ((AlgHom.id A E.Ring).prod (s.toAlgHom.comp E.π)).codRestrict _ fun x ↦
      (AlgHom.mem_equalizer _ _ _).2 (s.π_toAlgHom (E.π x)).symm
  π_toAlgHom x := by simp
  toAlgHom_ι m := by
    rw [AlgHom.comp_apply, toBaerSum_eq_ι_iff]
    exact ⟨m, 0, by simp, add_zero m⟩

end Split

section Neg

variable (E : SquareZeroExtension.{w} A B M)

/-- The splitting `π e ↦ (e, e)` of the Baer sum of `E` with its negation. -/
private noncomputable def baerSumNegSplitting : (E.baerSum E.neg).Splitting where
  toAlgHom := E.π.liftOfSurjective E.π_surjective
    ((E.toBaerSum E.neg).comp <|
      ((AlgHom.id A E.Ring).prod (AlgHom.id A E.Ring)).codRestrict _ fun x ↦ by simp)
    fun x hx ↦ by
      obtain ⟨m, rfl⟩ := (E.exact x).1 (RingHom.mem_ker.1 hx)
      exact RingHom.mem_ker.2 (toBaerSum_eq_zero_iff.2 ⟨m, by simp⟩)
  π_toAlgHom b := by
    obtain ⟨x, rfl⟩ := E.π_surjective b
    rw [AlgHom.liftOfSurjective_apply]
    simp

end Neg

end SquareZeroExtension

namespace Exal

variable {A : Type u} {B : Type v} {M : Type t} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module B M]

open SquareZeroExtension

/-- The Baer sum on `Exal_A(B, M)`. -/
noncomputable instance : Add (Exal A B M) where
  add := Exal.lift
    (fun E ↦ Exal.lift (fun F ↦ (E.baerSum F).extensionClass) fun _ _ ⟨g⟩ ↦
      extensionClass_eq_extensionClass_iff.2 ⟨baerSumMap (𝟙 E) g⟩)
    fun _ _ ⟨f⟩ ↦ funext fun y ↦ by
      induction y using Exal.ind with | h F => ?_
      simp only [lift_extensionClass]
      exact extensionClass_eq_extensionClass_iff.2 ⟨baerSumMap f (𝟙 F)⟩

/-- Negation on `Exal_A(B, M)`, by negating the kernel identification. -/
noncomputable instance : Neg (Exal A B M) where
  neg := Exal.lift (fun E ↦ E.neg.extensionClass) fun _ _ ⟨f⟩ ↦
    extensionClass_eq_extensionClass_iff.2 ⟨Hom.neg f⟩

end Exal

namespace SquareZeroExtension

variable {A : Type u} {B : Type v} {M : Type t} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module B M]

/-- The class of the Baer sum is the sum of the classes. -/
@[simp]
theorem extensionClass_baerSum (E F : SquareZeroExtension.{max v t} A B M) :
    (E.baerSum F).extensionClass = E.extensionClass + F.extensionClass := by
  -- Unfold the `Add` instance on `Exal A B M`, which is defined by `Exal.lift` in each argument.
  simp only [HAdd.hAdd, Add.add, Exal.lift_extensionClass]

/-- The class of the negated extension is the negative of the class. -/
@[simp]
theorem extensionClass_neg (E : SquareZeroExtension.{max v t} A B M) :
    E.neg.extensionClass = -E.extensionClass := by
  -- Unfold the `Neg` instance on `Exal A B M`, which is defined by `Exal.lift`.
  simp only [Neg.neg, Exal.lift_extensionClass]

end SquareZeroExtension

namespace Exal

variable {A : Type u} {B : Type v} {M : Type t} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module A M]
  [IsScalarTower A B M] [IsScalarTower A Bᵐᵒᵖ M]

open SquareZeroExtension

/-- `Exal_A(B, M)` is an abelian group under the Baer sum, with zero the class of the trivial
extension and negation given by negating the kernel identification. -/
noncomputable instance : AddCommGroup (Exal A B M) where
  add_assoc x y z := by
    induction x using Exal.ind with | h E => ?_
    induction y using Exal.ind with | h F => ?_
    induction z using Exal.ind with | h G => ?_
    rw [← extensionClass_baerSum, ← extensionClass_baerSum, ← extensionClass_baerSum,
      ← extensionClass_baerSum, extensionClass_eq_extensionClass_iff]
    exact ⟨baerSumAssoc⟩
  add_comm x y := by
    induction x using Exal.ind with | h E => ?_
    induction y using Exal.ind with | h F => ?_
    rw [← extensionClass_baerSum, ← extensionClass_baerSum, extensionClass_eq_extensionClass_iff]
    exact ⟨baerSumComm⟩
  add_zero x := by
    induction x using Exal.ind with | h E => ?_
    rw [← extensionClass_squareZero, ← extensionClass_baerSum, eq_comm,
      extensionClass_eq_extensionClass_iff]
    exact ⟨toBaerSumOfSplitting (squareZeroSplitting A B M)⟩
  zero_add x := by
    induction x using Exal.ind with | h E => ?_
    rw [← extensionClass_squareZero, ← extensionClass_baerSum, eq_comm,
      extensionClass_eq_extensionClass_iff]
    exact ⟨toBaerSumOfSplitting (squareZeroSplitting A B M) ≫ baerSumComm⟩
  neg_add_cancel x := by
    induction x using Exal.ind with | h E => ?_
    rw [← extensionClass_neg, ← extensionClass_baerSum, extensionClass_eq_zero_iff]
    exact ⟨(baerSumNegSplitting E).map baerSumComm⟩
  nsmul := nsmulRec
  zsmul := zsmulRec

end Exal

end TauCeti
