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

## Main results

* `TauCeti.Isogeny.Hom.dual_shafarevichTateMap_shafarevichTateMap`,
  `TauCeti.Isogeny.Hom.shafarevichTateMap_dual_shafarevichTateMap`: composing with the dual is
  multiplication by the degree.
* `TauCeti.Isogeny.Hom.ker_shafarevichTateMap_le_torsionBy`: the kernel is killed by the degree.
* `TauCeti.Isogeny.Hom.exists_isogeny_shafarevichTateMap_eq_zero`: if `Sha(W₂)` is finite, a
  nonzero multiple of a nonzero morphism is an isogeny inducing zero on Sha, as does its dual.
* `TauCeti.Isogeny.Hom.finite_shafarevichTateGroup_iff`: finiteness transfers along a morphism
  when the degree-torsion of both Shafarevich–Tate groups is finite.
* `TauCeti.Isogeny.Hom.finite_sha_iff`: over a number field, `Sha(W₁/K)` is finite if and only if
  `Sha(W₂/K)` is, for any nonzero morphism `W₁ → W₂`.

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
    fun c ↦ f.pointH1Map_mem_shafarevichTateGroup τ c.2

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

/-- If `n` kills `Sha(W₂)`, then the dual of `n • f`, which is `n • f̂`, induces the zero map
`Sha(W₂) → Sha(W₁)`. -/
theorem dual_nsmul_shafarevichTateMap_eq_zero {n : ℕ}
    (hn : ∀ c : W₂.shafarevichTateGroup τ, n • c = 0) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).dual.shafarevichTateMap τ = 0 := by
  refine AddMonoidHom.ext fun c ↦ ?_
  rw [dual_nsmul, shafarevichTateMap_nsmul, AddMonoidHom.nsmul_apply, ← AddMonoidHom.map_nsmul,
    hn, map_zero, AddMonoidHom.zero_apply]

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
  · rw [← dual_ofIsogeny, ofIsogeny_toIsogeny]
    exact dual_nsmul_shafarevichTateMap_eq_zero τ hn f

/-! ### Number fields -/

section NumberField

variable {K : Type*} [Field K] [NumberField K] {W₁ W₂ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Isogeny invariance of the finiteness of `Sha(E/K)`** over a number field `K`: for a nonzero
morphism `f : W₁ → W₂` over `K`, the Shafarevich–Tate group of `W₁` is finite if and only if that
of `W₂` is, local triviality being required at every finite and infinite place. -/
theorem finite_sha_iff (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0) :
    Finite W₁.sha ↔ Finite W₂.sha := by
  let τ (v : GlobalNumberFields.Place K) :
      SeparableClosure K →ₐ[K] SeparableClosure v.Completion := IsSepClosed.lift
  have : NeZero f.degree := ⟨(f.degree_eq_zero_iff).not.2 hf⟩
  have h₁ := W₁.finite_torsionBy_sha f.degree
  have h₂ := W₂.finite_torsionBy_sha f.degree
  rw [W₁.sha_eq_shafarevichTateGroup τ] at h₁ ⊢
  rw [W₂.sha_eq_shafarevichTateGroup τ] at h₂ ⊢
  exact f.finite_shafarevichTateGroup_iff τ

end NumberField

end TauCeti.Isogeny.Hom
