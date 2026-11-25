/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Ker
public import TauCeti.RepresentationTheory.WeilDeligne.Basic
public import TauCeti.RepresentationTheory.Character.Twist
public import TauCeti.RepresentationTheory.Dual
public import TauCeti.RepresentationTheory.Stabilizer
public import TauCeti.LinearAlgebra.Dual.Exp
public import TauCeti.LinearAlgebra.End.Prod
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.RepresentationTheory.Quotient

/-!
# Operations on raw Weil–Deligne parameters

For raw Weil–Deligne parameters `(V, r, N)` and `(V', r', N')`
(`TauCeti.WeilDeligneParameter`), this file constructs

* the **direct sum** `(V × V', r ⊕ r', N ⊕ N')` (`TauCeti.WeilDeligneParameter.prod`);
* the **dual** `(V^∨, r^∨, -Nᵗ)`, where `r^∨(w) = r(w⁻¹)ᵗ`
  (`TauCeti.WeilDeligneParameter.dual`);
* the **twist** `(V, χ r, N)` by a character `χ : W →* Eˣ` with open kernel
  (`TauCeti.WeilDeligneParameter.twist`);
* the **tensor product** `(V ⊗ V', r ⊗ r', N ⊗ 1 + 1 ⊗ N')`
  (`TauCeti.WeilDeligneParameter.tensor`).

The conjugation relation `r(w) N r(w)⁻¹ = q ^ deg w • N` holds for each because conjugation by
`r(w)` scales `N ⊗ 1` and `1 ⊗ N'` by the same factor, commutes with the transpose up to inverting
`w`, and is unchanged by a scalar. The kernel of the sum is the intersection of the two kernels,
and over a field the dual has the same kernel as the parameter. For the twist and the tensor
product the kernel only contains an open subgroup, so these need multiplication on `W` to be
separately continuous. Each operation is functorial on morphisms and isomorphisms of parameters
(the dual contravariantly), compatibly with inverses of isomorphisms, and the sum and the twist
commute with transport. The direct sum comes with its inclusions, projections, the pairing of
two morphisms into it and the copairing of two morphisms out of it, and twisting by characters
is an action of the character group. For finite-dimensional `V` the double dual is isomorphic
to the parameter through the canonical evaluation map
(`TauCeti.WeilDeligneParameter.dualDualIso`), so double duality recovers `N`.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568.
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §4.1.
-/

public section

noncomputable section

namespace TauCeti

open Module TensorProduct

namespace WeilDeligneParameter

variable {E W V V' V₁ V₂ V₁' V₂' V₃ V₃' : Type*} [Field E] [Group W] [TopologicalSpace W]
  [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V₁] [Module E V₁] [AddCommGroup V₂] [Module E V₂]
  [AddCommGroup V₁'] [Module E V₁'] [AddCommGroup V₂'] [Module E V₂']
  [AddCommGroup V₃] [Module E V₃] [AddCommGroup V₃'] [Module E V₃']
  {deg : W →* Multiplicative ℤ} {q : ℕ}

/-- The conjugation relation evaluated at a vector: `r(w) (N (r(w⁻¹) v)) = q ^ deg w • N v`. -/
theorem r_apply_N_apply_r_inv_apply (D : WeilDeligneParameter E W V deg q) (w : W) (v : V) :
    D.r w (D.N (D.r w⁻¹ v)) = (q : E) ^ (deg w).toAdd • D.N v :=
  LinearMap.congr_fun (D.conj_N w) v

/-! ### Direct sums -/

/-- The **direct sum** `(V × V', r ⊕ r', N ⊕ N')` of two raw Weil–Deligne parameters. -/
def prod (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q) :
    WeilDeligneParameter E W (V × V') deg q where
  r := D.r.prod D'.r
  isOpen_ker := by
    rw [Representation.ker_prod, Subgroup.coe_inf]
    exact D.isOpen_ker.inter D'.isOpen_ker
  N := D.N.prodMap D'.N
  isNilpotent_N := D.isNilpotent_N.prodMap D'.isNilpotent_N
  conj_N w := by
    refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
    · simpa using D.r_apply_N_apply_r_inv_apply w x.1
    · simpa using D'.r_apply_N_apply_r_inv_apply w x.2

variable (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q)

@[simp]
theorem prod_r : (D.prod D').r = D.r.prod D'.r :=
  (rfl)

@[simp]
theorem prod_N : (D.prod D').N = D.N.prodMap D'.N :=
  (rfl)

variable {D₁ : WeilDeligneParameter E W V₁ deg q} {D₂ : WeilDeligneParameter E W V₂ deg q}
  {D₁' : WeilDeligneParameter E W V₁' deg q} {D₂' : WeilDeligneParameter E W V₂' deg q}
  {D₃ : WeilDeligneParameter E W V₃ deg q} {D₃' : WeilDeligneParameter E W V₃' deg q}

/-- The direct sum of two morphisms of parameters. -/
def Hom.prodMap (f : Hom D₁ D₂) (g : Hom D₁' D₂') : Hom (D₁.prod D₁') (D₂.prod D₂') where
  toLinearMap := f.toLinearMap.prodMap g.toLinearMap
  isIntertwining' w := LinearMap.ext fun x ↦ Prod.ext (f.map_r_apply w x.1) (g.map_r_apply w x.2)
  comp_N := LinearMap.ext fun x ↦ Prod.ext (f.map_N_apply x.1) (g.map_N_apply x.2)

@[simp]
theorem Hom.prodMap_apply (f : Hom D₁ D₂) (g : Hom D₁' D₂') (x : V₁ × V₁') :
    f.prodMap g x = (f x.1, g x.2) :=
  (rfl)

@[simp]
theorem Hom.prodMap_id : (Hom.id D₁).prodMap (Hom.id D₁') = Hom.id (D₁.prod D₁') :=
  Hom.ext (LinearMap.ext fun x ↦ by simp)

@[simp]
theorem Hom.prodMap_comp (f : Hom D₂ D₃) (g : Hom D₂' D₃') (f' : Hom D₁ D₂)
    (g' : Hom D₁' D₂') : (f.comp f').prodMap (g.comp g') = (f.prodMap g).comp (f'.prodMap g') :=
  Hom.ext (LinearMap.ext fun x ↦ by simp)

/-- The inclusion of the first summand into a direct sum of parameters. -/
def Hom.inl : Hom D (D.prod D') where
  toLinearMap := LinearMap.inl E V V'
  isIntertwining' _ := LinearMap.ext fun _ ↦ by simp
  comp_N := LinearMap.ext fun _ ↦ by simp

/-- The inclusion of the second summand into a direct sum of parameters. -/
def Hom.inr : Hom D' (D.prod D') where
  toLinearMap := LinearMap.inr E V V'
  isIntertwining' _ := LinearMap.ext fun _ ↦ by simp
  comp_N := LinearMap.ext fun _ ↦ by simp

/-- The projection of a direct sum of parameters onto its first summand. -/
def Hom.fst : Hom (D.prod D') D where
  toLinearMap := LinearMap.fst E V V'
  isIntertwining' _ := LinearMap.ext fun _ ↦ by simp
  comp_N := LinearMap.ext fun _ ↦ by simp

/-- The projection of a direct sum of parameters onto its second summand. -/
def Hom.snd : Hom (D.prod D') D' where
  toLinearMap := LinearMap.snd E V V'
  isIntertwining' _ := LinearMap.ext fun _ ↦ by simp
  comp_N := LinearMap.ext fun _ ↦ by simp

/-- The morphism into a direct sum of parameters given by a pair of morphisms. -/
def Hom.prod (f : Hom D₃ D₁) (g : Hom D₃ D₁') : Hom D₃ (D₁.prod D₁') where
  toLinearMap := f.toLinearMap.prod g.toLinearMap
  isIntertwining' w := LinearMap.ext fun x ↦ Prod.ext (f.map_r_apply w x) (g.map_r_apply w x)
  comp_N := LinearMap.ext fun x ↦ Prod.ext (f.map_N_apply x) (g.map_N_apply x)

@[simp]
theorem Hom.inl_apply (v : V) : Hom.inl D D' v = (v, 0) :=
  (rfl)

@[simp]
theorem Hom.inr_apply (v : V') : Hom.inr D D' v = (0, v) :=
  (rfl)

@[simp]
theorem Hom.fst_apply (x : V × V') : Hom.fst D D' x = x.1 :=
  (rfl)

@[simp]
theorem Hom.snd_apply (x : V × V') : Hom.snd D D' x = x.2 :=
  (rfl)

@[simp]
theorem Hom.prod_apply (f : Hom D₃ D₁) (g : Hom D₃ D₁') (x : V₃) : f.prod g x = (f x, g x) :=
  (rfl)

@[simp]
theorem Hom.fst_comp_prod (f : Hom D₃ D₁) (g : Hom D₃ D₁') : (Hom.fst D₁ D₁').comp (f.prod g) = f :=
  Hom.ext (LinearMap.ext fun x ↦ by simp)

@[simp]
theorem Hom.snd_comp_prod (f : Hom D₃ D₁) (g : Hom D₃ D₁') :
    (Hom.snd D₁ D₁').comp (f.prod g) = g :=
  Hom.ext (LinearMap.ext fun x ↦ by simp)

/-- A morphism into a direct sum of parameters is the pairing of its two components. -/
@[simp]
theorem Hom.prod_unique (h : Hom D₃ (D₁.prod D₁')) :
    ((Hom.fst D₁ D₁').comp h).prod ((Hom.snd D₁ D₁').comp h) = h :=
  Hom.ext (LinearMap.ext fun x ↦ by simp)

/-- The morphism out of a direct sum of parameters given by a pair of morphisms. -/
def Hom.coprod (f : Hom D₁ D₃) (g : Hom D₁' D₃) : Hom (D₁.prod D₁') D₃ where
  toLinearMap := f.toLinearMap.coprod g.toLinearMap
  isIntertwining' w := LinearMap.ext fun x ↦ by
    simp [f.map_r_apply, g.map_r_apply]
  comp_N := LinearMap.ext fun x ↦ by
    simp [f.map_N_apply, g.map_N_apply]

@[simp]
theorem Hom.coprod_apply (f : Hom D₁ D₃) (g : Hom D₁' D₃) (x : V₁ × V₁') :
    f.coprod g x = f x.1 + g x.2 :=
  (rfl)

@[simp]
theorem Hom.coprod_comp_inl (f : Hom D₁ D₃) (g : Hom D₁' D₃) :
    (f.coprod g).comp (Hom.inl D₁ D₁') = f :=
  Hom.ext (LinearMap.ext fun x ↦ by simp)

@[simp]
theorem Hom.coprod_comp_inr (f : Hom D₁ D₃) (g : Hom D₁' D₃) :
    (f.coprod g).comp (Hom.inr D₁ D₁') = g :=
  Hom.ext (LinearMap.ext fun x ↦ by simp)

/-- A morphism out of a direct sum of parameters is the copairing of its restrictions to the two
summands. -/
@[simp]
theorem Hom.coprod_unique (h : Hom (D₁.prod D₁') D₃) :
    (h.comp (Hom.inl D₁ D₁')).coprod (h.comp (Hom.inr D₁ D₁')) = h :=
  Hom.ext (LinearMap.ext fun x ↦ by simp [← map_add])

/-- The direct sum of two isomorphisms of parameters. -/
def Iso.prodCongr (f : Iso D₁ D₂) (g : Iso D₁' D₂') : Iso (D₁.prod D₁') (D₂.prod D₂') :=
  Iso.ofBijective (f.toHom.prodMap g.toHom) (by
    rw [show ⇑(f.toHom.prodMap g.toHom) = Prod.map f g from
      funext fun x ↦ Prod.ext (by simp) (by simp)]
    exact Prod.map_bijective.mpr ⟨f.bijective, g.bijective⟩)

@[simp]
theorem Iso.prodCongr_apply (f : Iso D₁ D₂) (g : Iso D₁' D₂') (x : V₁ × V₁') :
    f.prodCongr g x = (f x.1, g x.2) := by
  simp [Iso.prodCongr]

@[simp]
theorem Iso.toHom_prodCongr (f : Iso D₁ D₂) (g : Iso D₁' D₂') :
    (f.prodCongr g).toHom = f.toHom.prodMap g.toHom :=
  Hom.ext (LinearMap.ext fun x ↦ by simp)

@[simp]
theorem Iso.prodCongr_refl : (Iso.refl D₁).prodCongr (Iso.refl D₁') = Iso.refl (D₁.prod D₁') :=
  Iso.ext (LinearEquiv.ext fun x ↦ by simp)

@[simp]
theorem Iso.prodCongr_trans (f : Iso D₁ D₂) (g : Iso D₁' D₂') (f' : Iso D₂ D₃)
    (g' : Iso D₂' D₃') :
    (f.trans f').prodCongr (g.trans g') = (f.prodCongr g).trans (f'.prodCongr g') :=
  Iso.ext (LinearEquiv.ext fun x ↦ by simp)

@[simp]
theorem Iso.prodCongr_symm (f : Iso D₁ D₂) (g : Iso D₁' D₂') :
    (f.prodCongr g).symm = f.symm.prodCongr g.symm :=
  Iso.ext (LinearEquiv.ext fun x ↦ (f.prodCongr g).injective (by simp))

/-- The direct sum commutes with transport. -/
theorem prod_transport (e : V ≃ₗ[E] V₁) (e' : V' ≃ₗ[E] V₁') :
    (D.transport e).prod (D'.transport e') = (D.prod D').transport (e.prodCongr e') := by
  ext w x <;> simp [transport_r_apply, transport_N_apply]

/-! ### Duals -/

/-- The **dual** `(V^∨, r^∨, -Nᵗ)` of a raw Weil–Deligne parameter, with
`r^∨(w) = r(w⁻¹)ᵗ`. -/
def dual : WeilDeligneParameter E W (Module.Dual E V) deg q where
  r := D.r.dual
  isOpen_ker := by
    rw [Representation.ker_dual]
    exact D.isOpen_ker
  N := -D.N.dualMap
  isNilpotent_N := IsNilpotent.neg (R := Module.End E (Module.Dual E V)) D.isNilpotent_N.dualMap
  conj_N w := by
    ext φ v
    simp [Representation.dual_apply, Module.Dual.transpose_apply,
      r_apply_N_apply_r_inv_apply]

@[simp]
theorem dual_r : D.dual.r = D.r.dual :=
  (rfl)

/-- Duality changes the monodromy `N` to `-Nᵗ`. -/
@[simp]
theorem dual_N : D.dual.N = -D.N.dualMap :=
  (rfl)

/-- The transpose of a morphism of parameters, a morphism between the duals in the opposite
direction. -/
def Hom.dual (f : Hom D₁ D₂) : Hom D₂.dual D₁.dual where
  toLinearMap := f.toLinearMap.dualMap
  isIntertwining' w := by
    ext φ v
    simp [Representation.dual_apply, Module.Dual.transpose_apply, f.map_r_apply]
  comp_N := by
    ext φ v
    simp [f.map_N_apply]

@[simp]
theorem Hom.dual_apply (f : Hom D₁ D₂) (φ : Module.Dual E V₂) : f.dual φ = φ ∘ₗ f.toLinearMap :=
  (rfl)

@[simp]
theorem Hom.dual_id : (Hom.id D₁).dual = Hom.id D₁.dual :=
  Hom.ext (LinearMap.ext fun φ ↦ by simp)

@[simp]
theorem Hom.dual_comp (f : Hom D₂ D₃) (g : Hom D₁ D₂) : (f.comp g).dual = g.dual.comp f.dual :=
  Hom.ext (LinearMap.ext fun φ ↦ by simp [LinearMap.comp_assoc])

/-- The transpose of an isomorphism of parameters. -/
def Iso.dual (f : Iso D₁ D₂) : Iso D₂.dual D₁.dual :=
  Iso.ofBijective f.toHom.dual (by
    rw [show ⇑f.toHom.dual = f.toLinearEquiv.dualMap from funext fun φ ↦ by ext; simp]
    exact f.toLinearEquiv.dualMap.bijective)

@[simp]
theorem Iso.dual_apply (f : Iso D₁ D₂) (φ : Module.Dual E V₂) :
    f.dual φ = φ ∘ₗ f.toLinearEquiv.toLinearMap := by
  simp [Iso.dual]

@[simp]
theorem Iso.toHom_dual (f : Iso D₁ D₂) : f.dual.toHom = f.toHom.dual :=
  Hom.ext (LinearMap.ext fun φ ↦ by simp)

@[simp]
theorem Iso.dual_refl : (Iso.refl D₁).dual = Iso.refl D₁.dual :=
  Iso.ext (LinearEquiv.ext fun φ ↦ LinearMap.ext fun v ↦ by simp)

@[simp]
theorem Iso.dual_trans (f : Iso D₁ D₂) (g : Iso D₂ D₃) :
    (f.trans g).dual = g.dual.trans f.dual :=
  Iso.ext (LinearEquiv.ext fun φ ↦ LinearMap.ext fun v ↦ by simp)

@[simp]
theorem Iso.dual_symm (f : Iso D₁ D₂) : f.dual.symm = f.symm.dual :=
  Iso.ext (LinearEquiv.ext fun φ ↦ f.dual.injective (LinearMap.ext fun v ↦ by simp))

/-- **Double duality.** For finite-dimensional `V`, the canonical evaluation map is an
isomorphism from a parameter to its double dual; in particular the monodromy of the double dual
is `N`. -/
def dualDualIso [FiniteDimensional E V] : Iso D D.dual.dual where
  toLinearEquiv := Module.evalEquiv E V
  isIntertwining' w := by
    ext v φ
    simp [Representation.dual_apply, Module.Dual.transpose_apply]
  comp_N := by
    ext v φ
    simp

@[simp]
theorem dualDualIso_apply [FiniteDimensional E V] (v : V) :
    D.dualDualIso v = Module.Dual.eval E V v :=
  (rfl)

/-! ### Twists -/

variable [SeparatelyContinuousMul W]

/-- The **twist** `(V, χ r, N)` of a raw Weil–Deligne parameter by a character `χ : W →* Eˣ`
with open kernel. -/
def twist (χ : W →* Eˣ) (hχ : IsOpen (χ.ker : Set W)) : WeilDeligneParameter E W V deg q where
  r := Representation.charTwist χ D.r
  isOpen_ker :=
    Subgroup.isOpen_mono (Representation.ker_inf_ker_le_ker_charTwist χ D.r) (hχ.inter D.isOpen_ker)
  N := D.N
  isNilpotent_N := D.isNilpotent_N
  conj_N w := by
    ext v
    simpa [Representation.charTwist_apply_apply, smul_smul] using
      D.r_apply_N_apply_r_inv_apply w v

variable (χ : W →* Eˣ) (hχ : IsOpen (χ.ker : Set W))

@[simp]
theorem twist_r : (D.twist χ hχ).r = Representation.charTwist χ D.r :=
  (rfl)

@[simp]
theorem twist_N : (D.twist χ hχ).N = D.N :=
  (rfl)

/-- Twisting by the trivial character changes nothing. -/
@[simp]
theorem twist_one (h : IsOpen ((1 : W →* Eˣ).ker : Set W)) : D.twist 1 h = D := by
  ext w v <;> simp

/-- Twisting twice multiplies the characters. -/
@[simp]
theorem twist_twist (ψ : W →* Eˣ) (hψ : IsOpen (ψ.ker : Set W)) :
    (D.twist χ hχ).twist ψ hψ =
      D.twist (ψ * χ) (Subgroup.isOpen_mono (ψ.ker_inf_ker_le_ker_mul χ) (hψ.inter hχ)) := by
  ext w v <;> simp [Representation.charTwist_charTwist]

/-- The twist of a morphism of parameters by a common character. -/
def Hom.twist (f : Hom D₁ D₂) : Hom (D₁.twist χ hχ) (D₂.twist χ hχ) where
  toLinearMap := f.toLinearMap
  isIntertwining' w := LinearMap.ext fun v ↦ by
    simp [f.map_r_apply]
  comp_N := f.comp_N

@[simp]
theorem Hom.twist_apply (f : Hom D₁ D₂) (v : V₁) : f.twist χ hχ v = f v :=
  (rfl)

@[simp]
theorem Hom.twist_id : (Hom.id D₁).twist χ hχ = Hom.id (D₁.twist χ hχ) :=
  Hom.ext (LinearMap.ext fun v ↦ by simp)

@[simp]
theorem Hom.twist_comp (f : Hom D₂ D₃) (g : Hom D₁ D₂) :
    (f.comp g).twist χ hχ = (f.twist χ hχ).comp (g.twist χ hχ) :=
  Hom.ext (LinearMap.ext fun v ↦ by simp)

/-- The twist of an isomorphism of parameters by a common character. -/
def Iso.twist (f : Iso D₁ D₂) : Iso (D₁.twist χ hχ) (D₂.twist χ hχ) :=
  Iso.ofBijective (f.toHom.twist χ hχ) (by
    rw [show ⇑(f.toHom.twist χ hχ) = f from funext fun v ↦ by simp]
    exact f.bijective)

@[simp]
theorem Iso.twist_apply (f : Iso D₁ D₂) (v : V₁) : f.twist χ hχ v = f v := by
  simp [Iso.twist]

@[simp]
theorem Iso.toHom_twist (f : Iso D₁ D₂) : (f.twist χ hχ).toHom = f.toHom.twist χ hχ :=
  Hom.ext (LinearMap.ext fun v ↦ by simp)

@[simp]
theorem Iso.twist_refl : (Iso.refl D₁).twist χ hχ = Iso.refl (D₁.twist χ hχ) :=
  Iso.ext (LinearEquiv.ext fun v ↦ by simp)

@[simp]
theorem Iso.twist_trans (f : Iso D₁ D₂) (g : Iso D₂ D₃) :
    (f.trans g).twist χ hχ = (f.twist χ hχ).trans (g.twist χ hχ) :=
  Iso.ext (LinearEquiv.ext fun v ↦ by simp)

@[simp]
theorem Iso.twist_symm (f : Iso D₁ D₂) : (f.twist χ hχ).symm = f.symm.twist χ hχ :=
  Iso.ext (LinearEquiv.ext fun v ↦ (f.twist χ hχ).injective (by simp))

/-- The twist commutes with transport. -/
theorem twist_transport (e : V ≃ₗ[E] V₁) :
    (D.transport e).twist χ hχ = (D.twist χ hχ).transport e := by
  ext w v <;> simp [transport_r_apply, transport_N_apply]

/-! ### Tensor products -/

/-- The **tensor product** `(V ⊗ V', r ⊗ r', N ⊗ 1 + 1 ⊗ N')` of two raw Weil–Deligne
parameters. -/
def tensor : WeilDeligneParameter E W (V ⊗[E] V') deg q where
  r := D.r.tprod D'.r
  isOpen_ker :=
    Subgroup.isOpen_mono (Representation.ker_inf_ker_le_ker_tprod D.r D'.r)
      (D.isOpen_ker.inter D'.isOpen_ker)
  N := D.N.rTensor V' + D'.N.lTensor V
  isNilpotent_N := by
    refine Commute.isNilpotent_add ?_ ?_ ?_
    · ext v v'
      simp
    · exact D.isNilpotent_N.map (Module.End.rTensorAlgHom E V V')
    · exact D'.isNilpotent_N.map (Module.End.lTensorAlgHom E V' V)
  conj_N w := by
    ext v v'
    simp [Representation.tprod_apply, r_apply_N_apply_r_inv_apply, Representation.self_inv_apply,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul]

@[simp]
theorem tensor_r : (D.tensor D').r = D.r.tprod D'.r :=
  (rfl)

@[simp]
theorem tensor_N : (D.tensor D').N = D.N.rTensor V' + D'.N.lTensor V :=
  (rfl)

/-- The tensor product of two morphisms of parameters. -/
def Hom.tensor (f : Hom D₁ D₂) (g : Hom D₁' D₂') : Hom (D₁.tensor D₁') (D₂.tensor D₂') where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  isIntertwining' w := by
    ext v v'
    simp [Representation.tprod_apply, f.map_r_apply, g.map_r_apply]
  comp_N := by
    ext v v'
    simp [f.map_N_apply, g.map_N_apply]

@[simp]
theorem Hom.tensor_tmul (f : Hom D₁ D₂) (g : Hom D₁' D₂') (v : V₁) (v' : V₁') :
    f.tensor g (v ⊗ₜ v') = f v ⊗ₜ g v' :=
  (rfl)

@[simp]
theorem Hom.tensor_id : (Hom.id D₁).tensor (Hom.id D₁') = Hom.id (D₁.tensor D₁') :=
  Hom.ext (TensorProduct.ext' fun v v' ↦ by simp)

@[simp]
theorem Hom.tensor_comp (f : Hom D₂ D₃) (g : Hom D₂' D₃') (f' : Hom D₁ D₂) (g' : Hom D₁' D₂') :
    (f.comp f').tensor (g.comp g') = (f.tensor g).comp (f'.tensor g') :=
  Hom.ext (TensorProduct.ext' fun v v' ↦ by simp)

/-- The tensor product of two isomorphisms of parameters. -/
def Iso.tensor (f : Iso D₁ D₂) (g : Iso D₁' D₂') : Iso (D₁.tensor D₁') (D₂.tensor D₂') :=
  Iso.ofBijective (f.toHom.tensor g.toHom) (by
    rw [show ⇑(f.toHom.tensor g.toHom) = TensorProduct.congr f.toLinearEquiv g.toLinearEquiv by
      ext x
      induction x using TensorProduct.inductionOn with
      | tmul v v' => simp
      | add x y hx hy => simp [hx, hy]]
    exact (TensorProduct.congr f.toLinearEquiv g.toLinearEquiv).bijective)

@[simp]
theorem Iso.tensor_tmul (f : Iso D₁ D₂) (g : Iso D₁' D₂') (v : V₁) (v' : V₁') :
    f.tensor g (v ⊗ₜ v') = f v ⊗ₜ g v' := by
  simp [Iso.tensor]

@[simp]
theorem Iso.toHom_tensor (f : Iso D₁ D₂) (g : Iso D₁' D₂') :
    (f.tensor g).toHom = f.toHom.tensor g.toHom :=
  Hom.ext (TensorProduct.ext' fun v v' ↦ by simp)

@[simp]
theorem Iso.tensor_refl : (Iso.refl D₁).tensor (Iso.refl D₁') = Iso.refl (D₁.tensor D₁') :=
  Iso.ext (LinearEquiv.toLinearMap_injective (TensorProduct.ext' fun v v' ↦ by simp))

@[simp]
theorem Iso.tensor_trans (f : Iso D₁ D₂) (g : Iso D₁' D₂') (f' : Iso D₂ D₃)
    (g' : Iso D₂' D₃') :
    (f.trans f').tensor (g.trans g') = (f.tensor g).trans (f'.tensor g') :=
  Iso.ext (LinearEquiv.toLinearMap_injective (TensorProduct.ext' fun v v' ↦ by simp))

@[simp]
theorem Iso.tensor_symm (f : Iso D₁ D₂) (g : Iso D₁' D₂') :
    (f.tensor g).symm = f.symm.tensor g.symm :=
  Iso.ext (LinearEquiv.toLinearMap_injective (TensorProduct.ext' fun v v' ↦
    (f.tensor g).injective (by simp)))

end WeilDeligneParameter

end TauCeti
