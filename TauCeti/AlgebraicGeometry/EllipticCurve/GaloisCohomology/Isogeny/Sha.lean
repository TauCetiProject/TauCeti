/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Map
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.NumberField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Add
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange

/-!
# Isogenies on Shafarevich–Tate groups

Let `f : W₁ → W₂` be a morphism of elliptic curves over a field `K`, and fix a family of field
extensions `L i` of `K` with embeddings `τ i : Kˢ → (L i)ˢ`. Since the map induced by `f` on
`H¹(G_K, E(Kˢ))` commutes with restriction to every `L i`, it preserves the classes that are
locally trivial along the family, and so restricts to a homomorphism of Shafarevich–Tate groups

```text
f.shafarevichTateMap τ : Sha(W₁) → Sha(W₂).
```

These maps are additive in `f` and functorial. Composing with the dual isogeny `f̂` gives
multiplication by `deg f` in either order, so the kernel of `f.shafarevichTateMap τ` lies in the
`deg f`-torsion of `Sha(W₁)`. Hence, whenever the `deg f`-torsion of both groups is finite, one
group is finite exactly when the other is (`TauCeti.Isogeny.Hom.finite_shafarevichTateGroup_iff`).

If `n` kills `Sha(W₂)`, then both `n • f` and its dual `(n • f)^ = n • f̂` induce the zero map on
Shafarevich–Tate groups. When `Sha(W₂)` is finite, its order is such an `n`, so every nonzero `f`
has a nonzero multiple `ψ = n • f`, an isogeny, for which `Sha(W₁)[ψ] = Sha(W₁)` and
`Sha(W₂)[ψ̂] = Sha(W₂)` (`TauCeti.Isogeny.Hom.exists_isogeny_shafarevichTateMap_eq_zero`). This is
how the orders of the full Shafarevich–Tate groups enter the descent sequences of an isogeny and
its dual, as in Cassels' comparison of Birch–Swinnerton-Dyer quotients of isogenous curves.

Over a number field the `m`-torsion of `Sha(E/K)` is finite for every `m ≠ 0`
(`WeierstrassCurve.finite_torsionBy_sha`, from the finiteness of the `m`-Selmer group). This gives
the **isogeny invariance of the finiteness of `Sha(E/K)`**
(`TauCeti.Isogeny.Hom.finite_sha_iff`): for a nonzero morphism `W₁ → W₂` over `K`, `Sha(W₁/K)` is
finite if and only if `Sha(W₂/K)` is. Finiteness itself is conjectural; this is the form in which
it enters the isogeny invariance of the Birch–Swinnerton-Dyer quotient (Cassels).

## Main definitions

* `TauCeti.Isogeny.Hom.shafarevichTateMap`: the map `Sha(W₁) → Sha(W₂)` induced by a morphism.
* `TauCeti.Isogeny.Hom.shafarevichTateMapEquivOfDegreeEqOne`: the group isomorphism
  `Sha(W₁) ≃+ Sha(W₂)` induced by a degree-one morphism.
* `TauCeti.Isogeny.Hom.shaMap`: over a number field, the induced map `Sha(W₁/K) → Sha(W₂/K)`
  independent of any choice of embeddings.
* `TauCeti.Isogeny.Hom.shaMapEquivOfDegreeEqOne`: over a number field, the group isomorphism
  `Sha(W₁/K) ≃+ Sha(W₂/K)` induced by a degree-one morphism.

## Main results

* `TauCeti.Isogeny.Hom.dual_shafarevichTateMap_shafarevichTateMap`,
  `TauCeti.Isogeny.Hom.shafarevichTateMap_dual_shafarevichTateMap`: composing with the dual is
  multiplication by the degree.
* `TauCeti.Isogeny.Hom.ker_shafarevichTateMap_le_torsionBy`: the kernel is killed by the degree.
* `TauCeti.Isogeny.Hom.exists_isogeny_shafarevichTateMap_eq_zero`: if `Sha(W₂)` is finite, a
  nonzero multiple of a nonzero morphism is an isogeny inducing zero on Sha, as does its dual.
* `TauCeti.Isogeny.Hom.finite_shafarevichTateGroup_iff`: finiteness transfers along a morphism
  when the degree-torsion of both Shafarevich–Tate groups is finite.
* `TauCeti.Isogeny.Hom.inclusion_comp_shaMap`, `TauCeti.Isogeny.Hom.shaMap_eq_zero_iff`,
  `TauCeti.Isogeny.Hom.kerShaMapEquivKerShafarevichTateMap`,
  `TauCeti.Isogeny.Hom.card_ker_shaMap`, and `TauCeti.Isogeny.Hom.card_range_shaMap`:
  comparison of `shaMap` with `shafarevichTateMap τ` for any family `τ` of embeddings.
* `TauCeti.Isogeny.Hom.finite_ker_shaMap`, `TauCeti.Isogeny.Hom.finite_sha_iff`, and
  `TauCeti.Isogeny.Hom.exists_isogeny_shaMap_eq_zero`: over a number field, for any nonzero
  morphism `W₁ → W₂`, the kernel of `shaMap` is finite, `Sha(W₁/K)` is finite if and only if
  `Sha(W₂/K)` is, and when `Sha(W₂/K)` is finite a nonzero multiple is an isogeny killing `Sha`
  in both directions.
* `TauCeti.Isogeny.Hom.card_sha_eq_of_degree_eq_one`: degree-one morphisms preserve `#Sha(E/K)`.
* `WeierstrassCurve.VariableChange.finite_sha_smul_iff`: finiteness of `Sha(E/K)` is invariant
  under a change of Weierstrass variables.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
* @sqrt-of-2, [Tau Ceti PR #20914](https://github.com/TauCetiProject/TauCeti/pull/20914), whose
  approach this file follows.
-/

public section

noncomputable section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve TauCeti.ContCohomology

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]
  {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))

/-! ### The map on Shafarevich–Tate groups -/

/-- A morphism over `K` sends locally trivial classes to locally trivial classes. -/
theorem pointH1Map_mem_shafarevichTateGroup (f : Hom W₁.toAffine W₂.toAffine)
    {c : H1 (AbsoluteGaloisGroup K) W₁.PointCoeff} (hc : c ∈ W₁.shafarevichTateGroup τ) :
    f.pointH1Map c ∈ W₂.shafarevichTateGroup τ := by
  rw [mem_shafarevichTateGroup_iff] at hc ⊢
  intro i
  rw [pointRes_pointH1Map, hc i]
  exact map_zero _

/-- **The map `Sha(W₁) → Sha(W₂)`** induced by a morphism `f : W₁ → W₂` over `K`: the restriction
of `f.pointH1Map` to the classes that are locally trivial along `τ`. -/
def shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine) :
    W₁.shafarevichTateGroup τ →+ W₂.shafarevichTateGroup τ :=
  (f.pointH1Map.comp (W₁.shafarevichTateGroup τ).subtype).codRestrict _
    fun c ↦ f.pointH1Map_mem_shafarevichTateGroup τ c.property

/-- The map on Shafarevich–Tate groups is the map on first cohomology. -/
@[simp]
theorem coe_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (c : W₁.shafarevichTateGroup τ) :
    (f.shafarevichTateMap τ c : H1 (AbsoluteGaloisGroup K) W₂.PointCoeff) = f.pointH1Map c :=
  (rfl)

/-- The identity morphism acts identically on the Shafarevich–Tate group. -/
@[simp]
theorem shafarevichTateMap_id : (id W₁.toAffine).shafarevichTateMap τ = AddMonoidHom.id _ := by
  ext c
  simp

/-- Composition of morphisms induces composition on Shafarevich–Tate groups. -/
@[simp]
theorem shafarevichTateMap_comp (g : Hom W₂.toAffine W₃.toAffine)
    (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).shafarevichTateMap τ = (g.shafarevichTateMap τ).comp (f.shafarevichTateMap τ) := by
  ext c
  simp

/-- Addition of morphisms adds their induced maps on Shafarevich–Tate groups. -/
@[simp]
theorem shafarevichTateMap_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).shafarevichTateMap τ = f.shafarevichTateMap τ + g.shafarevichTateMap τ := by
  ext c
  simp

/-- Negating a morphism negates its induced map on Shafarevich–Tate groups. -/
@[simp]
theorem shafarevichTateMap_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).shafarevichTateMap τ = -f.shafarevichTateMap τ := by
  ext c
  simp

/-- Subtraction of morphisms subtracts their induced maps on Shafarevich–Tate groups. -/
@[simp]
theorem shafarevichTateMap_sub (f g : Hom W₁.toAffine W₂.toAffine) :
    (f - g).shafarevichTateMap τ = f.shafarevichTateMap τ - g.shafarevichTateMap τ := by
  ext c
  simp

/-- The zero morphism induces zero on Shafarevich–Tate groups. -/
@[simp]
theorem shafarevichTateMap_zero : (0 : Hom W₁.toAffine W₂.toAffine).shafarevichTateMap τ = 0 := by
  ext c
  simp

/-- Multiplication by `n` on the curve induces multiplication by `n` on the Shafarevich–Tate
group. -/
@[simp]
theorem shafarevichTateMap_natCast (n : ℕ) (c : W₁.shafarevichTateGroup τ) :
    (n : Hom W₁.toAffine W₁.toAffine).shafarevichTateMap τ c = n • c := by
  ext
  simp

/-- Multiplying a morphism by `n` multiplies its induced map on Shafarevich–Tate groups by `n`. -/
@[simp]
theorem shafarevichTateMap_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).shafarevichTateMap τ = n • f.shafarevichTateMap τ := by
  have hf : n • f = (n : Hom W₂.toAffine W₂.toAffine).comp f := by
    rw [← nsmul_one, one_def, nsmul_comp, id_comp]
  refine AddMonoidHom.ext fun c ↦ ?_
  rw [hf, shafarevichTateMap_comp, AddMonoidHom.comp_apply, shafarevichTateMap_natCast,
    AddMonoidHom.nsmul_apply]

/-- If `n` kills `Sha(W₂)`, then `n • f` induces the zero map `Sha(W₁) → Sha(W₂)`. -/
theorem shafarevichTateMap_nsmul_eq_zero {n : ℕ}
    (hn : ∀ c : W₂.shafarevichTateGroup τ, n • c = 0) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).shafarevichTateMap τ = 0 := by
  refine AddMonoidHom.ext fun c ↦ ?_
  rw [shafarevichTateMap_nsmul, AddMonoidHom.nsmul_apply, hn, AddMonoidHom.zero_apply]

/-- If `n` kills `Sha(W₁)`, then `n • f` induces the zero map `Sha(W₁) → Sha(W₂)`. -/
theorem shafarevichTateMap_nsmul_eq_zero_of_domain {n : ℕ}
    (hn : ∀ c : W₁.shafarevichTateGroup τ, n • c = 0) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).shafarevichTateMap τ = 0 := by
  refine AddMonoidHom.ext fun c ↦ ?_
  rw [shafarevichTateMap_nsmul, AddMonoidHom.nsmul_apply, ← AddMonoidHom.map_nsmul, hn, map_zero,
    AddMonoidHom.zero_apply]

/-! ### The dual isogeny -/

/-- **A morphism followed by its dual is multiplication by the degree** on the Shafarevich–Tate
group. -/
@[simp]
theorem dual_shafarevichTateMap_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (c : W₁.shafarevichTateGroup τ) :
    f.dual.shafarevichTateMap τ (f.shafarevichTateMap τ c) = f.degree • c := by
  rw [← AddMonoidHom.comp_apply, ← shafarevichTateMap_comp, dual_comp_self, ← one_def, nsmul_one,
    shafarevichTateMap_natCast]

/-- **The dual of a morphism followed by the morphism is multiplication by the degree** on the
Shafarevich–Tate group. -/
@[simp]
theorem shafarevichTateMap_dual_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (c : W₂.shafarevichTateGroup τ) :
    f.shafarevichTateMap τ (f.dual.shafarevichTateMap τ c) = f.degree • c := by
  rw [← AddMonoidHom.comp_apply, ← shafarevichTateMap_comp, comp_dual_self, ← one_def, nsmul_one,
    shafarevichTateMap_natCast]

/-- **The kernel of the map on Shafarevich–Tate groups is killed by the degree.** -/
theorem ker_shafarevichTateMap_le_torsionBy (f : Hom W₁.toAffine W₂.toAffine) :
    (f.shafarevichTateMap τ).ker ≤ AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) f.degree :=
  fun c hc ↦ AddSubgroup.torsionBy.nsmul_iff.2 <| by
    rw [← dual_shafarevichTateMap_shafarevichTateMap, AddMonoidHom.mem_ker.1 hc, map_zero]

/-! ### Finiteness -/

/-- The kernel of the map on Shafarevich–Tate groups is finite whenever the degree-torsion
of the source is finite. -/
theorem finite_ker_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    [Finite (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) f.degree)] :
    Finite (f.shafarevichTateMap τ).ker :=
  Finite.of_injective _
    (AddSubgroup.inclusion_injective (f.ker_shafarevichTateMap_le_torsionBy τ))

/-- If the `deg f`-torsion of `Sha(W₁)` is finite, then `Sha(W₁)` is finite as soon as `Sha(W₂)`
is: the kernel of `f.shafarevichTateMap τ` lies in that torsion. -/
theorem finite_shafarevichTateGroup_of_finite (f : Hom W₁.toAffine W₂.toAffine)
    [Finite (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) f.degree)]
    [Finite (W₂.shafarevichTateGroup τ)] : Finite (W₁.shafarevichTateGroup τ) :=
  have := f.finite_ker_shafarevichTateMap τ
  (f.shafarevichTateMap τ).finite_iff_finite_ker_range.2 ⟨inferInstance, inferInstance⟩

/-- **Isogeny invariance of the finiteness of Shafarevich–Tate groups**: if the `deg f`-torsion
of both `Sha(W₁)` and `Sha(W₂)` is finite, then `Sha(W₁)` is finite if and only if `Sha(W₂)` is.
The converse direction goes through the dual of `f`, which has the same degree. -/
theorem finite_shafarevichTateGroup_iff (f : Hom W₁.toAffine W₂.toAffine)
    [Finite (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) f.degree)]
    [Finite (AddSubgroup.torsionBy (W₂.shafarevichTateGroup τ) f.degree)] :
    Finite (W₁.shafarevichTateGroup τ) ↔ Finite (W₂.shafarevichTateGroup τ) := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ f.finite_shafarevichTateGroup_of_finite τ⟩
  have : Finite (AddSubgroup.torsionBy (W₂.shafarevichTateGroup τ) f.dual.degree) := by
    rwa [degree_dual]
  exact f.dual.finite_shafarevichTateGroup_of_finite τ

/-- **A degree-one morphism induces an isomorphism on Shafarevich–Tate groups**, with inverse
induced by its dual. -/
def shafarevichTateMapEquivOfDegreeEqOne (f : Hom W₁.toAffine W₂.toAffine) (hf : f.degree = 1) :
    W₁.shafarevichTateGroup τ ≃+ W₂.shafarevichTateGroup τ where
  toFun := f.shafarevichTateMap τ
  invFun := f.dual.shafarevichTateMap τ
  left_inv c := by rw [dual_shafarevichTateMap_shafarevichTateMap, hf, one_smul]
  right_inv c := by rw [shafarevichTateMap_dual_shafarevichTateMap, hf, one_smul]
  map_add' := (f.shafarevichTateMap τ).map_add'

/-- Applying `shafarevichTateMapEquivOfDegreeEqOne` is `shafarevichTateMap`. -/
@[simp]
theorem shafarevichTateMapEquivOfDegreeEqOne_apply (f : Hom W₁.toAffine W₂.toAffine)
    (hf : f.degree = 1) (c : W₁.shafarevichTateGroup τ) :
    f.shafarevichTateMapEquivOfDegreeEqOne τ hf c = f.shafarevichTateMap τ c :=
  (rfl)

/-- Applying the inverse of `shafarevichTateMapEquivOfDegreeEqOne` is the dual map. -/
@[simp]
theorem shafarevichTateMapEquivOfDegreeEqOne_symm_apply (f : Hom W₁.toAffine W₂.toAffine)
    (hf : f.degree = 1) (c : W₂.shafarevichTateGroup τ) :
    (f.shafarevichTateMapEquivOfDegreeEqOne τ hf).symm c = f.dual.shafarevichTateMap τ c :=
  (rfl)

/-- The underlying additive homomorphism of `shafarevichTateMapEquivOfDegreeEqOne` is
`shafarevichTateMap`. -/
@[simp]
theorem shafarevichTateMapEquivOfDegreeEqOne_toAddMonoidHom
    (f : Hom W₁.toAffine W₂.toAffine) (hf : f.degree = 1) :
    (f.shafarevichTateMapEquivOfDegreeEqOne τ hf :
      W₁.shafarevichTateGroup τ →+ W₂.shafarevichTateGroup τ) = f.shafarevichTateMap τ :=
  (rfl)

/-- The underlying additive homomorphism of `(shafarevichTateMapEquivOfDegreeEqOne).symm` is
`f.dual.shafarevichTateMap`. -/
@[simp]
theorem shafarevichTateMapEquivOfDegreeEqOne_symm_toAddMonoidHom
    (f : Hom W₁.toAffine W₂.toAffine) (hf : f.degree = 1) :
    ((f.shafarevichTateMapEquivOfDegreeEqOne τ hf).symm :
      W₂.shafarevichTateGroup τ →+ W₁.shafarevichTateGroup τ) = f.dual.shafarevichTateMap τ :=
  (rfl)

/-- **Degree-one morphisms preserve the order of `Sha(W)`** for any family of local conditions. -/
theorem card_shafarevichTateGroup_eq_of_degree_eq_one (f : Hom W₁.toAffine W₂.toAffine)
    (hf : f.degree = 1) :
    Nat.card (W₁.shafarevichTateGroup τ) = Nat.card (W₂.shafarevichTateGroup τ) :=
  Nat.card_congr (f.shafarevichTateMapEquivOfDegreeEqOne τ hf).toEquiv

/-- **An isogeny killing Sha in both directions**: if `Sha(W₂)` is finite, then for every nonzero
morphism `f : W₁ → W₂` the multiple `ψ = #Sha(W₂) • f` is an isogeny such that both `ψ` and its
dual `ψ̂` induce the zero map on Shafarevich–Tate groups. -/
theorem exists_isogeny_shafarevichTateMap_eq_zero {f : Hom W₁.toAffine W₂.toAffine} (hf : f ≠ 0)
    [Finite (W₂.shafarevichTateGroup τ)] :
    ∃ ψ : Isogeny W₁.toAffine W₂.toAffine,
      ofIsogeny ψ = Nat.card (W₂.shafarevichTateGroup τ) • f ∧
        (ofIsogeny ψ).shafarevichTateMap τ = 0 ∧ (ofIsogeny ψ.dual).shafarevichTateMap τ = 0 := by
  have hn (c : W₂.shafarevichTateGroup τ) : Nat.card (W₂.shafarevichTateGroup τ) • c = 0 :=
    card_nsmul_eq_zero'
  have hψ : Nat.card (W₂.shafarevichTateGroup τ) • f ≠ 0 := by
    rw [Ne, ← degree_eq_zero_iff, degree_nsmul]
    exact mul_ne_zero (pow_ne_zero _ Nat.card_pos.ne') ((degree_eq_zero_iff f).not.2 hf)
  refine ⟨toIsogeny hψ, ofIsogeny_toIsogeny hψ, ?_, ?_⟩
  · rw [ofIsogeny_toIsogeny]
    exact shafarevichTateMap_nsmul_eq_zero τ hn f
  · rw [← dual_ofIsogeny, ofIsogeny_toIsogeny, dual_nsmul]
    exact shafarevichTateMap_nsmul_eq_zero_of_domain τ hn f.dual

/-! ### Independence of embeddings -/

/-- Changing the family of embeddings of separable closures commutes with `shafarevichTateMap`
under the canonical inclusions of Shafarevich–Tate groups. -/
theorem inclusion_comp_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (τ' : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i)) :
    (AddSubgroup.inclusion (W₂.shafarevichTateGroup_eq_shafarevichTateGroup τ τ').le).comp
        (f.shafarevichTateMap τ) =
      (f.shafarevichTateMap τ').comp
        (AddSubgroup.inclusion (W₁.shafarevichTateGroup_eq_shafarevichTateGroup τ τ').le) := by
  ext c
  rfl

/-- Whether `f.shafarevichTateMap τ` is zero does not depend on the choice of embeddings `τ`. -/
theorem shafarevichTateMap_eq_zero_iff (f : Hom W₁.toAffine W₂.toAffine)
    (τ' : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i)) :
    f.shafarevichTateMap τ = 0 ↔ f.shafarevichTateMap τ' = 0 := by
  have hinj : Function.Injective
      (AddSubgroup.inclusion (W₂.shafarevichTateGroup_eq_shafarevichTateGroup τ τ').le) :=
    AddSubgroup.inclusion_injective _
  have hsurj : Function.Surjective
      (AddSubgroup.inclusion (W₁.shafarevichTateGroup_eq_shafarevichTateGroup τ τ').le) :=
    (AddEquiv.addSubgroupCongr (W₁.shafarevichTateGroup_eq_shafarevichTateGroup τ τ')).surjective
  rw [← AddMonoidHom.cancel_left hinj, AddMonoidHom.comp_zero,
    f.inclusion_comp_shafarevichTateMap τ τ',
    ← AddMonoidHom.zero_comp
      (AddSubgroup.inclusion (W₁.shafarevichTateGroup_eq_shafarevichTateGroup τ τ').le),
    AddMonoidHom.cancel_right hsurj]

/-- Changing the family of embeddings of separable closures induces a canonical isomorphism on
the kernels of `shafarevichTateMap`. -/
def kerShafarevichTateMapEquiv (f : Hom W₁.toAffine W₂.toAffine)
    (τ' : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i)) :
    (f.shafarevichTateMap τ).ker ≃+ (f.shafarevichTateMap τ').ker where
  toFun c :=
    ⟨AddSubgroup.inclusion (W₁.shafarevichTateGroup_eq_shafarevichTateGroup τ τ').le c, by
      rw [AddMonoidHom.mem_ker, ← AddMonoidHom.comp_apply,
        ← f.inclusion_comp_shafarevichTateMap τ τ', AddMonoidHom.comp_apply,
        AddMonoidHom.mem_ker.1 c.property, map_zero]⟩
  invFun c :=
    ⟨AddSubgroup.inclusion (W₁.shafarevichTateGroup_eq_shafarevichTateGroup τ τ').ge c, by
      rw [AddMonoidHom.mem_ker,
        ← AddSubgroup.inclusion_inj (W₂.shafarevichTateGroup_eq_shafarevichTateGroup τ τ').le,
        map_zero, ← AddMonoidHom.comp_apply, f.inclusion_comp_shafarevichTateMap τ τ',
        AddMonoidHom.comp_apply]
      exact AddMonoidHom.mem_ker.1 c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Applying `kerShafarevichTateMapEquiv` preserves the underlying cohomology class. -/
@[simp]
theorem coe_kerShafarevichTateMapEquiv (f : Hom W₁.toAffine W₂.toAffine)
    (τ' : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))
    (c : (f.shafarevichTateMap τ).ker) :
    ((f.kerShafarevichTateMapEquiv τ τ' c : W₁.shafarevichTateGroup τ') :
        H1 (AbsoluteGaloisGroup K) W₁.PointCoeff) =
      (c : W₁.shafarevichTateGroup τ) :=
  (rfl)

/-- Applying the inverse of `kerShafarevichTateMapEquiv` preserves the underlying cohomology
class. -/
@[simp]
theorem coe_kerShafarevichTateMapEquiv_symm (f : Hom W₁.toAffine W₂.toAffine)
    (τ' : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))
    (c : (f.shafarevichTateMap τ').ker) :
    (((f.kerShafarevichTateMapEquiv τ τ').symm c : W₁.shafarevichTateGroup τ) :
        H1 (AbsoluteGaloisGroup K) W₁.PointCoeff) =
      (c : W₁.shafarevichTateGroup τ') :=
  (rfl)

/-- The order of `(f.shafarevichTateMap τ).ker` is independent of the choice of embeddings `τ`. -/
theorem card_ker_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (τ' : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i)) :
    Nat.card (f.shafarevichTateMap τ).ker = Nat.card (f.shafarevichTateMap τ').ker :=
  Nat.card_congr (f.kerShafarevichTateMapEquiv τ τ').toEquiv

/-- The image of `f.shafarevichTateMap τ` in `H¹(G_K, W₂(Kˢ))` is independent of the choice of
embeddings `τ`. -/
theorem map_subtype_range_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (τ' : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i)) :
    (f.shafarevichTateMap τ).range.map (W₂.shafarevichTateGroup τ).subtype =
      (f.shafarevichTateMap τ').range.map (W₂.shafarevichTateGroup τ').subtype := by
  have hsub : (W₂.shafarevichTateGroup τ).subtype =
      (W₂.shafarevichTateGroup τ').subtype.comp
        (AddSubgroup.inclusion (W₂.shafarevichTateGroup_eq_shafarevichTateGroup τ τ').le) := rfl
  have hrange :
      (AddSubgroup.inclusion
        (W₁.shafarevichTateGroup_eq_shafarevichTateGroup τ τ').le).range = ⊤ :=
    AddMonoidHom.range_eq_top.2
      (AddEquiv.addSubgroupCongr (W₁.shafarevichTateGroup_eq_shafarevichTateGroup τ τ')).surjective
  rw [← AddMonoidHom.range_comp, ← AddMonoidHom.range_comp, hsub, AddMonoidHom.comp_assoc,
    f.inclusion_comp_shafarevichTateMap τ τ', ← AddMonoidHom.comp_assoc,
    AddMonoidHom.range_comp, hrange, AddSubgroup.map_top]

/-- The order of `(f.shafarevichTateMap τ).range` is independent of the choice of embeddings
`τ`. -/
theorem card_range_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (τ' : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i)) :
    Nat.card (f.shafarevichTateMap τ).range = Nat.card (f.shafarevichTateMap τ').range := by
  rw [Nat.card_congr (AddSubgroup.equivMapOfInjective _ (W₂.shafarevichTateGroup τ).subtype
      Subtype.coe_injective).toEquiv,
    Nat.card_congr (AddSubgroup.equivMapOfInjective _ (W₂.shafarevichTateGroup τ').subtype
      Subtype.coe_injective).toEquiv, f.map_subtype_range_shafarevichTateMap τ τ']

/-- Changing the family of embeddings of separable closures intertwines the degree-one isomorphism
`shafarevichTateMapEquivOfDegreeEqOne` with the canonical identifications of Shafarevich–Tate
groups. -/
theorem shafarevichTateMapEquivOfDegreeEqOne_trans_addSubgroupCongr
    (f : Hom W₁.toAffine W₂.toAffine) (hf : f.degree = 1)
    (τ' : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i)) :
    (f.shafarevichTateMapEquivOfDegreeEqOne τ hf).trans
        (AddEquiv.addSubgroupCongr (W₂.shafarevichTateGroup_eq_shafarevichTateGroup τ τ')) =
      (AddEquiv.addSubgroupCongr (W₁.shafarevichTateGroup_eq_shafarevichTateGroup τ τ')).trans
        (f.shafarevichTateMapEquivOfDegreeEqOne τ' hf) :=
  AddEquiv.toAddMonoidHom_injective (f.inclusion_comp_shafarevichTateMap τ τ')

/-! ### Number fields -/

section NumberField

variable {K : Type*} [Field K] [NumberField K] {W₁ W₂ W₃ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

private abbrev defaultPlaceEmbeddings (K : Type*) [Field K] [NumberField K] :
    ∀ v : GlobalNumberFields.Place K, SeparableClosure K →ₐ[K] SeparableClosure v.Completion :=
  fun _ ↦ IsSepClosed.lift

private abbrev shaCongr (W : WeierstrassCurve K) :
    W.sha ≃+ W.shafarevichTateGroup (defaultPlaceEmbeddings K) :=
  AddEquiv.addSubgroupCongr (W.sha_eq_shafarevichTateGroup (defaultPlaceEmbeddings K))

/-- A morphism over a number field `K` sends classes of `Sha(W₁/K)` into `Sha(W₂/K)`. -/
theorem pointH1Map_mem_sha (f : Hom W₁.toAffine W₂.toAffine)
    {c : H1 (AbsoluteGaloisGroup K) W₁.PointCoeff} (hc : c ∈ W₁.sha) :
    f.pointH1Map c ∈ W₂.sha := by
  rw [W₁.sha_eq_shafarevichTateGroup (defaultPlaceEmbeddings K)] at hc
  rw [W₂.sha_eq_shafarevichTateGroup (defaultPlaceEmbeddings K)]
  exact f.pointH1Map_mem_shafarevichTateGroup (defaultPlaceEmbeddings K) hc

/-- **The map `Sha(W₁/K) → Sha(W₂/K)`** induced by a morphism `f : W₁ → W₂` over a number field
`K`: the restriction of `f.pointH1Map` to the Shafarevich–Tate groups. -/
def shaMap (f : Hom W₁.toAffine W₂.toAffine) : W₁.sha →+ W₂.sha :=
  ((shaCongr W₂).symm.toAddMonoidHom.comp
    (f.shafarevichTateMap (defaultPlaceEmbeddings K))).comp
    (shaCongr W₁).toAddMonoidHom

/-- The map on `Sha(E/K)` is the map on first cohomology. -/
@[simp]
theorem coe_shaMap (f : Hom W₁.toAffine W₂.toAffine) (c : W₁.sha) :
    (f.shaMap c : H1 (AbsoluteGaloisGroup K) W₂.PointCoeff) = f.pointH1Map c :=
  f.coe_shafarevichTateMap (defaultPlaceEmbeddings K) (shaCongr W₁ c)

/-- The identity morphism acts identically on `Sha(E/K)`. -/
@[simp]
theorem shaMap_id : (id W₁.toAffine).shaMap = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun c ↦ by simp [shaMap, shafarevichTateMap_id]

/-- Composition of morphisms induces composition on `Sha(E/K)`. -/
@[simp]
theorem shaMap_comp (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).shaMap = g.shaMap.comp f.shaMap :=
  AddMonoidHom.ext fun c ↦ by simp [shaMap, shafarevichTateMap_comp]

/-- Addition of morphisms adds their induced maps on `Sha(E/K)`. -/
@[simp]
theorem shaMap_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).shaMap = f.shaMap + g.shaMap :=
  AddMonoidHom.ext fun c ↦ by simp [shaMap, shafarevichTateMap_add]

/-- Negating a morphism negates its induced map on `Sha(E/K)`. -/
@[simp]
theorem shaMap_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).shaMap = -f.shaMap :=
  AddMonoidHom.ext fun c ↦ by simp [shaMap, shafarevichTateMap_neg]

/-- Subtraction of morphisms subtracts their induced maps on `Sha(E/K)`. -/
@[simp]
theorem shaMap_sub (f g : Hom W₁.toAffine W₂.toAffine) :
    (f - g).shaMap = f.shaMap - g.shaMap :=
  AddMonoidHom.ext fun c ↦ by simp [shaMap, shafarevichTateMap_sub]

/-- The zero morphism induces zero on `Sha(E/K)`. -/
@[simp]
theorem shaMap_zero : (0 : Hom W₁.toAffine W₂.toAffine).shaMap = 0 :=
  AddMonoidHom.ext fun c ↦ by simp [shaMap, shafarevichTateMap_zero]

/-- Multiplication by `n` on the curve induces multiplication by `n` on `Sha(E/K)`. -/
@[simp]
theorem shaMap_natCast (n : ℕ) (c : W₁.sha) :
    (n : Hom W₁.toAffine W₁.toAffine).shaMap c = n • c := by
  simp [shaMap]

/-- Multiplying a morphism by `n` multiplies its induced map on `Sha(E/K)` by `n`. -/
@[simp]
theorem shaMap_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).shaMap = n • f.shaMap :=
  AddMonoidHom.ext fun c ↦ by simp [shaMap, shafarevichTateMap_nsmul]

/-- **A morphism followed by its dual is multiplication by the degree** on `Sha(E/K)`. -/
@[simp]
theorem dual_shaMap_shaMap (f : Hom W₁.toAffine W₂.toAffine) (c : W₁.sha) :
    f.dual.shaMap (f.shaMap c) = f.degree • c := by
  simp [shaMap]

/-- **The dual of a morphism followed by the morphism is multiplication by the degree** on
`Sha(E/K)`. -/
@[simp]
theorem shaMap_dual_shaMap (f : Hom W₁.toAffine W₂.toAffine) (c : W₂.sha) :
    f.shaMap (f.dual.shaMap c) = f.degree • c := by
  simp [shaMap]

/-- Along any family `τ` of embeddings of separable closures over the places of `K`, `f.shaMap`
agrees with `f.shafarevichTateMap τ` under the canonical identifications of `Sha` with
`shafarevichTateGroup τ`. -/
theorem inclusion_comp_shaMap (f : Hom W₁.toAffine W₂.toAffine)
    (τ : ∀ v : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion) :
    (AddSubgroup.inclusion (W₂.sha_eq_shafarevichTateGroup τ).le).comp f.shaMap =
      (f.shafarevichTateMap τ).comp
        (AddSubgroup.inclusion (W₁.sha_eq_shafarevichTateGroup τ).le) := by
  ext c
  exact congrArg Subtype.val
    (congrFun (congrArg DFunLike.coe
      (f.inclusion_comp_shafarevichTateMap (defaultPlaceEmbeddings K) τ)) (shaCongr W₁ c))

/-- Along any family `τ` of embeddings of separable closures over the places of `K`, `f.shaMap`
is zero if and only if `f.shafarevichTateMap τ` is zero. -/
theorem shaMap_eq_zero_iff (f : Hom W₁.toAffine W₂.toAffine)
    (τ : ∀ v : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion) :
    f.shaMap = 0 ↔ f.shafarevichTateMap τ = 0 := by
  simp only [← f.shafarevichTateMap_eq_zero_iff (defaultPlaceEmbeddings K) τ,
    AddMonoidHom.ext_iff, AddMonoidHom.zero_apply, shaMap, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.map_eq_zero_iff]
  exact (shaCongr W₁).forall_congr_left

private def kerShaMapEquivKerDefault (f : Hom W₁.toAffine W₂.toAffine) :
    f.shaMap.ker ≃+ (f.shafarevichTateMap (defaultPlaceEmbeddings K)).ker where
  toFun c := ⟨shaCongr W₁ c, by
    rw [AddMonoidHom.mem_ker, ← (shaCongr W₂).symm.map_eq_zero_iff]
    exact AddMonoidHom.mem_ker.1 c.property⟩
  invFun c := ⟨(shaCongr W₁).symm c, by
    simp [AddMonoidHom.mem_ker, shaMap, AddMonoidHom.mem_ker.1 c.property]⟩
  left_inv _ := Subtype.ext (AddEquiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (AddEquiv.apply_symm_apply _ _)
  map_add' _ _ := rfl

/-- Along any family `τ` of embeddings over the places of `K`, the kernel `f.shaMap.ker` is
canonically isomorphic to `(f.shafarevichTateMap τ).ker`. -/
def kerShaMapEquivKerShafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (τ : ∀ v : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion) :
    f.shaMap.ker ≃+ (f.shafarevichTateMap τ).ker :=
  (kerShaMapEquivKerDefault f).trans (f.kerShafarevichTateMapEquiv (defaultPlaceEmbeddings K) τ)

/-- Applying `kerShaMapEquivKerShafarevichTateMap` preserves the underlying cohomology class. -/
@[simp]
theorem coe_kerShaMapEquivKerShafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine)
    (τ : ∀ v : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion)
    (c : f.shaMap.ker) :
    ((f.kerShaMapEquivKerShafarevichTateMap τ c : W₁.shafarevichTateGroup τ) :
        H1 (AbsoluteGaloisGroup K) W₁.PointCoeff) =
      (c : W₁.sha) :=
  (rfl)

/-- Applying the inverse of `kerShaMapEquivKerShafarevichTateMap` preserves the underlying
cohomology class. -/
@[simp]
theorem coe_kerShaMapEquivKerShafarevichTateMap_symm (f : Hom W₁.toAffine W₂.toAffine)
    (τ : ∀ v : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion)
    (c : (f.shafarevichTateMap τ).ker) :
    (((f.kerShaMapEquivKerShafarevichTateMap τ).symm c : W₁.sha) :
        H1 (AbsoluteGaloisGroup K) W₁.PointCoeff) =
      (c : W₁.shafarevichTateGroup τ) :=
  (rfl)

/-- Over a number field `K`, the order of `f.shaMap.ker` equals the order of
`(f.shafarevichTateMap τ).ker` for any family `τ` of embeddings over the places of `K`. -/
theorem card_ker_shaMap (f : Hom W₁.toAffine W₂.toAffine)
    (τ : ∀ v : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion) :
    Nat.card f.shaMap.ker = Nat.card (f.shafarevichTateMap τ).ker :=
  Nat.card_congr (f.kerShaMapEquivKerShafarevichTateMap τ).toEquiv

/-- The image of `f.shaMap` in `H¹(G_K, W₂(Kˢ))` agrees with that of `f.shafarevichTateMap τ`
for any family `τ` of embeddings over the places of `K`. -/
theorem map_subtype_range_shaMap (f : Hom W₁.toAffine W₂.toAffine)
    (τ : ∀ v : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion) :
    f.shaMap.range.map W₂.sha.subtype =
      (f.shafarevichTateMap τ).range.map (W₂.shafarevichTateGroup τ).subtype := by
  have hsub : W₂.sha.subtype =
      (W₂.shafarevichTateGroup τ).subtype.comp
        (AddSubgroup.inclusion (W₂.sha_eq_shafarevichTateGroup τ).le) := rfl
  have hrange : (AddSubgroup.inclusion (W₁.sha_eq_shafarevichTateGroup τ).le).range = ⊤ :=
    AddMonoidHom.range_eq_top.2
      (AddEquiv.addSubgroupCongr (W₁.sha_eq_shafarevichTateGroup τ)).surjective
  rw [← AddMonoidHom.range_comp, ← AddMonoidHom.range_comp, hsub, AddMonoidHom.comp_assoc,
    f.inclusion_comp_shaMap τ, ← AddMonoidHom.comp_assoc, AddMonoidHom.range_comp, hrange,
    AddSubgroup.map_top]

/-- The order of the image of `f.shaMap` equals the order of the image of `f.shafarevichTateMap τ`
for any family `τ` of embeddings over the places of `K`. -/
theorem card_range_shaMap (f : Hom W₁.toAffine W₂.toAffine)
    (τ : ∀ v : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion) :
    Nat.card f.shaMap.range = Nat.card (f.shafarevichTateMap τ).range := by
  rw [Nat.card_congr
      (AddSubgroup.equivMapOfInjective _ W₂.sha.subtype Subtype.coe_injective).toEquiv,
    Nat.card_congr (AddSubgroup.equivMapOfInjective _ (W₂.shafarevichTateGroup τ).subtype
      Subtype.coe_injective).toEquiv, f.map_subtype_range_shaMap τ]

/-- **The kernel of `f.shaMap` is killed by the degree of `f`.** -/
theorem ker_shaMap_le_torsionBy (f : Hom W₁.toAffine W₂.toAffine) :
    f.shaMap.ker ≤ AddSubgroup.torsionBy W₁.sha f.degree := by
  intro c hc
  have hc' := f.ker_shafarevichTateMap_le_torsionBy (defaultPlaceEmbeddings K) (by
    rw [AddMonoidHom.mem_ker, ← (shaCongr W₂).symm.map_eq_zero_iff]
    exact AddMonoidHom.mem_ker.1 hc :
      shaCongr W₁ c ∈ (f.shafarevichTateMap (defaultPlaceEmbeddings K)).ker)
  rw [AddSubgroup.torsionBy.nsmul_iff] at hc' ⊢
  rw [← (shaCongr W₁).map_eq_zero_iff, _root_.map_nsmul]
  exact hc'

/-- Over a number field `K`, the kernel of `f.shaMap` is finite for every nonzero morphism
`f : W₁ → W₂`. -/
theorem finite_ker_shaMap (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0) :
    Finite f.shaMap.ker := by
  have : NeZero f.degree := ⟨(f.degree_eq_zero_iff).not.2 hf⟩
  have h := W₁.finite_torsionBy_sha f.degree
  rw [W₁.sha_eq_shafarevichTateGroup (defaultPlaceEmbeddings K)] at h
  have := f.finite_ker_shafarevichTateMap (defaultPlaceEmbeddings K)
  exact Finite.of_equiv _
    (f.kerShaMapEquivKerShafarevichTateMap (defaultPlaceEmbeddings K)).symm.toEquiv

/-- **Isogeny invariance of the finiteness of `Sha(E/K)`** over a number field `K`: for a nonzero
morphism `f : W₁ → W₂` over `K`, the Shafarevich–Tate group of `W₁` is finite if and only if that
of `W₂` is, local triviality being required at every finite and infinite place. -/
theorem finite_sha_iff (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0) :
    Finite W₁.sha ↔ Finite W₂.sha := by
  have : NeZero f.degree := ⟨(f.degree_eq_zero_iff).not.2 hf⟩
  have h₁ := W₁.finite_torsionBy_sha f.degree
  have h₂ := W₂.finite_torsionBy_sha f.degree
  rw [W₁.sha_eq_shafarevichTateGroup (defaultPlaceEmbeddings K)] at h₁ ⊢
  rw [W₂.sha_eq_shafarevichTateGroup (defaultPlaceEmbeddings K)] at h₂ ⊢
  exact f.finite_shafarevichTateGroup_iff (defaultPlaceEmbeddings K)

/-- **A degree-one morphism induces an isomorphism on `Sha(E/K)`** over any number field `K`,
with inverse induced by its dual. -/
def shaMapEquivOfDegreeEqOne (f : Hom W₁.toAffine W₂.toAffine) (hf : f.degree = 1) :
    W₁.sha ≃+ W₂.sha :=
  ((shaCongr W₁).trans (f.shafarevichTateMapEquivOfDegreeEqOne (defaultPlaceEmbeddings K) hf)).trans
    (shaCongr W₂).symm

/-- Applying `shaMapEquivOfDegreeEqOne` is `shaMap`. -/
@[simp]
theorem shaMapEquivOfDegreeEqOne_apply (f : Hom W₁.toAffine W₂.toAffine) (hf : f.degree = 1)
    (c : W₁.sha) :
    f.shaMapEquivOfDegreeEqOne hf c = f.shaMap c :=
  (rfl)

/-- Applying the inverse of `shaMapEquivOfDegreeEqOne` is the dual map. -/
@[simp]
theorem shaMapEquivOfDegreeEqOne_symm_apply (f : Hom W₁.toAffine W₂.toAffine) (hf : f.degree = 1)
    (c : W₂.sha) :
    (f.shaMapEquivOfDegreeEqOne hf).symm c = f.dual.shaMap c :=
  (rfl)

/-- The underlying additive homomorphism of `shaMapEquivOfDegreeEqOne` is `shaMap`. -/
@[simp]
theorem shaMapEquivOfDegreeEqOne_toAddMonoidHom (f : Hom W₁.toAffine W₂.toAffine)
    (hf : f.degree = 1) :
    (f.shaMapEquivOfDegreeEqOne hf : W₁.sha →+ W₂.sha) = f.shaMap :=
  (rfl)

/-- The underlying additive homomorphism of `(shaMapEquivOfDegreeEqOne).symm` is
`f.dual.shaMap`. -/
@[simp]
theorem shaMapEquivOfDegreeEqOne_symm_toAddMonoidHom (f : Hom W₁.toAffine W₂.toAffine)
    (hf : f.degree = 1) :
    ((f.shaMapEquivOfDegreeEqOne hf).symm : W₂.sha →+ W₁.sha) = f.dual.shaMap :=
  (rfl)

/-- Along any family `τ` of embeddings over the places of `K`, the degree-one isomorphism
`f.shaMapEquivOfDegreeEqOne hf` agrees with `f.shafarevichTateMapEquivOfDegreeEqOne τ hf` under
the canonical identifications of `Sha` with `shafarevichTateGroup τ`. -/
theorem shaMapEquivOfDegreeEqOne_trans_addSubgroupCongr (f : Hom W₁.toAffine W₂.toAffine)
    (hf : f.degree = 1)
    (τ : ∀ v : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion) :
    (f.shaMapEquivOfDegreeEqOne hf).trans
        (AddEquiv.addSubgroupCongr (W₂.sha_eq_shafarevichTateGroup τ)) =
      (AddEquiv.addSubgroupCongr (W₁.sha_eq_shafarevichTateGroup τ)).trans
        (f.shafarevichTateMapEquivOfDegreeEqOne τ hf) :=
  AddEquiv.toAddMonoidHom_injective (f.inclusion_comp_shaMap τ)

/-- **Degree-one morphisms preserve the order of `Sha(E/K)`** over any number field `K`. -/
theorem card_sha_eq_of_degree_eq_one (f : Hom W₁.toAffine W₂.toAffine) (hf : f.degree = 1) :
    Nat.card W₁.sha = Nat.card W₂.sha := by
  rw [W₁.sha_eq_shafarevichTateGroup (defaultPlaceEmbeddings K),
    W₂.sha_eq_shafarevichTateGroup (defaultPlaceEmbeddings K)]
  exact f.card_shafarevichTateGroup_eq_of_degree_eq_one (defaultPlaceEmbeddings K) hf

/-- **An isogeny killing `Sha(E/K)` in both directions**: over a number field `K`, if `Sha(W₂/K)`
is finite, then for every nonzero morphism `f : W₁ → W₂` the multiple `ψ = #Sha(W₂/K) • f` is an
isogeny such that both `ψ` and its dual `ψ̂` induce the zero map on `Sha`. -/
theorem exists_isogeny_shaMap_eq_zero {f : Hom W₁.toAffine W₂.toAffine} (hf : f ≠ 0)
    [Finite W₂.sha] :
    ∃ ψ : Isogeny W₁.toAffine W₂.toAffine,
      ofIsogeny ψ = Nat.card W₂.sha • f ∧
        (ofIsogeny ψ).shaMap = 0 ∧ (ofIsogeny ψ.dual).shaMap = 0 := by
  have : Finite (W₂.shafarevichTateGroup (defaultPlaceEmbeddings K)) := by
    rwa [← W₂.sha_eq_shafarevichTateGroup (defaultPlaceEmbeddings K)]
  obtain ⟨ψ, hψ, h₁, h₂⟩ :=
    f.exists_isogeny_shafarevichTateMap_eq_zero (defaultPlaceEmbeddings K) hf
  rw [← W₂.sha_eq_shafarevichTateGroup (defaultPlaceEmbeddings K)] at hψ
  exact ⟨ψ, hψ,
    ((ofIsogeny ψ).shaMap_eq_zero_iff (defaultPlaceEmbeddings K)).2 h₁,
    ((ofIsogeny ψ.dual).shaMap_eq_zero_iff (defaultPlaceEmbeddings K)).2 h₂⟩

end NumberField

end TauCeti.Isogeny.Hom

namespace WeierstrassCurve.VariableChange

/-- **Finiteness of `Sha(E/K)` is invariant under a change of Weierstrass variables** over any
number field `K`. -/
@[simp]
theorem finite_sha_smul_iff {K : Type*} [Field K] [NumberField K]
    (C : VariableChange K) (E : WeierstrassCurve K) [E.IsElliptic] :
    Finite (C • E).sha ↔ Finite E.sha :=
  ((TauCeti.Isogeny.Hom.ofIsogeny (TauCeti.Isogeny.variableChangeIsogeny C rfl)).finite_sha_iff
    (TauCeti.Isogeny.Hom.ofIsogeny_ne_zero _)).symm

/-- Finiteness of `Sha(E/K)` transfers across a change of Weierstrass variables. -/
instance finite_sha_smul {K : Type*} [Field K] [NumberField K]
    (C : VariableChange K) (E : WeierstrassCurve K) [E.IsElliptic] [Finite E.sha] :
    Finite (C • E).sha :=
  (finite_sha_smul_iff C E).2 inferInstance

end WeierstrassCurve.VariableChange
